-- Prove2me | Theorems.Thm_AlgoPFR_Supplement_theorem_4_2_ggmt_access
-- name    : AlgoPFR.Supplement.theorem_4_2_ggmt_access
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:36:25.873409+00:00
-- url     : https://prove2.me/theorems/8cbdc8be-550c-444b-a74e-9f5968acadf7
-- title:
--   Theorem 4.2 — from samples and membership queries to $A$, algorithmic access to a near-subspace variable $X_T$ with probability $\Omega(1/\mathrm{polylog}\,K)$
-- statement:
--   There are three fixed programs — a main program $P$ and two interpreters $P_{\mathrm{samp}}$, $P_{\mathrm{coin}}$ — and constants $C$, $c_0>0$, $c$, $c_1$ such that the following holds for every $n$, every nonempty $A\subseteq\mathbb F_2^n$ and every natural number $K$ with $|A+A|\le K|A|$. Given uniform samples from $A$ and a membership oracle for $A$:
--
--   1. on every run, $P$ halts after at most $CK^c$ samples, at most $CK^c$ membership queries and log-cost time at most $C(n+1)K^c$;
--   2. with probability at least
--   $$\frac{c_0}{(\log(2K))^{c_1}}$$
--   $P$ outputs a description $o$ of algorithmic access to a random variable $X_T$, in the following sense. $X_T$ is the $X$-component of the state reached from $X_0=Y_0=U_A$ after $T$ recorded iterations of Algorithm 2, with its envelope $M_{X_T}$, and
--      - $T\le C(\log\log(4K)+1)$;
--      - the access is exact: $\Pr[\mathrm{Coin}_{X_T}(x)=1]=p_{X_T}(x)/M_{X_T}$ for every $x$ (Definition 4.1);
--      - $\Delta[X_T]=H[X_T]+\log M_{X_T}\le C$;
--      - $d[X_T;U_H]\le C$ for some subspace $H\le\mathbb F_2^n$, and $d[U_A;X_T]\le C(\log K+2)$;
--      - run on $o$ with the same oracles and fresh randomness, $P_{\mathrm{samp}}$ outputs each $y$ with probability exactly $p_{X_T}(y)$, and $P_{\mathrm{coin}}$ on input $x$ outputs $1$ with probability exactly $\Pr[\mathrm{Coin}_{X_T}(x)=1]$ and $0$ otherwise;
--      - one call to $P_{\mathrm{samp}}$, or to $P_{\mathrm{coin}}$ on any input $x$, uses in expectation at most $CK^c$ samples, at most $CK^c$ queries and log-cost time at most $C(n+1)K^c$.
--
--   This is the algorithmic form of the GGMT entropy-decrement tree: with probability $1/\mathrm{polylog}\,K$ it reaches, in $O(n\cdot\mathrm{poly}(K))$ time, a random variable close to a subspace with cheap exact sampling and density access. Section 5 of the source extracts the subspace of Theorem 1.2 from this access.
--
--   **Formalization Note** Logarithms are base 2. Machine, tapes and probabilities are those of `AlgoPFR.Machine`; the trajectory, the states and the envelopes are those of `AlgoPFR.Iteration`. The programs and all constants are fixed before $n$, $A$ and $K$; $P$ reads $[n,K]$, the interpreters read $n$, $K$, the coin input and $o$. The success probability is in inner-measure form, and the exact-law clauses are stated as lower bounds on the probabilities of disjoint outputs whose bounds sum to $1$, which forces equality.
--
--   Differences from the source:
--
--   - encoding: outputs algorithmic access to a random variable X_T (a pair of algorithms Sample, Coin) → P outputs a description o; fixed interpreter programs run on o with the same oracles and fresh randomness implement Sample_{X_T} and Coin_{X_T} exactly; reason: makes 'outputs access' a property of what programs of the base machine compute; Definition 4.1's procedures are algorithms
--   - encoding: X_T, where T = O(log log K) → X_T is the X-component (with envelope M_X) of the state reached from rootState A by folding the published nextState over a recorded trajectory τ, with |τ| ≤ C(log₂ log₂(4K) + 1); reason: Claim 4.14 describes X_T as the end of a length-T trajectory Γ = (F_t, Z_t, J_{X,t}, J_{Y,t}); this makes T checkable
--   - encoding: Ω(1/polylog K), O(1), O(log K), poly(K), O(n·poly(K)) → c₀/(log₂ 2K)^{c₁} with c₀ > 0, C, C(log₂ K + 2), C·K^c, C(n + 1)K^c, constants before n, A, K; reason: one program for all inputs; the offsets keep the bounds meaningful at K = 1, 2 and n = 0
--   - generalization: overall sample and query complexity poly(K), time O(n·poly(K)) → the bounds hold on every run (every tape whose samples lie in A); reason: the stronger reading; Claim 4.15's budget makes Algorithm 2 'always use' these resources
--   - reading: the cost of one call to the access procedures is poly(K) samples and queries, O(n·poly(K)) time → the expectation over the call's own randomness is at most C·K^c (samples, queries) and C(n + 1)K^c (time), for every description on the success event and every coin input x; reason: Claim 4.15: 'each later call … has expected sample complexity poly(K)'; a rejection sampler has no worst-case bound
--   - encoding: a randomized algorithm and 'time' → programs of the randomized log-cost oracle RAM of AlgoPFR.Machine; reason: the source names no model; the base mission fixes this one
--   - encoding: with probability at least … → the event contains a measurable event of at least that measure; reason: inner measure, as in the base mission
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Theorem 4.2, p.18 (proof: Claims 4.13–4.15 and §4.5, pp.35–40)

import Mathlib
import Definitions.Def_AlgoPFR_Machine
import Definitions.Def_AlgoPFR_Iteration
import Definitions.Def_AlgoPFR_Supplement_ExpectedWithin

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

namespace Supplement

/-- **Theorem 4.2.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*,
arXiv:2609.20771 (sha256 60e45066…), p.18: let `K ∈ ℕ` and let `A ⊆ F₂ⁿ` be nonempty with
`|A + A| ≤ K|A|`. Given membership and uniform-sampling access to `A`, there is a randomized
algorithm that, with probability at least `Ω(1/polylog(K))`, outputs algorithmic access to a random
variable `X_T`, where `T = O(log log K)`, such that, for some subspace `H ≤ F₂ⁿ`, `d[X_T;U_H] = O(1)`,
`d[U_A;X_T] = O(log K)` and `Δ[X_T] = O(1)`. The algorithm has overall sample and query complexity
`poly(K)` and runs in time `O(n · poly(K))`. One call to the access procedures of `X_T` has sample and
query complexity `poly(K)` and time complexity `O(n · poly(K))` as well.

**Formalization Note.** The main program `P`, the two interpreter programs `Psamp`, `Pcoin` and all
constants come before `n, A, K`. `P` reads `[n, K]`. "Outputs algorithmic access" means: `P` halts with
a description `o`, and `Psamp` run on `n :: K :: o` (resp. `Pcoin` on `n :: K :: encodeVec x :: o`), with
the same two oracles of `A` and fresh randomness, outputs `[encodeVec y]` with probability exactly
`p_{X_T}(y)` (resp. `[1]` with probability `Pr[Coin_{X_T}(x) = 1]` and `[0]` otherwise). The lower bounds
`ProbAtLeast … (p y)` already force equality, since the output events are disjoint and the masses sum to
`1`. `X_T` is the `X`-component of the state reached from `X₀ = Y₀ = U_A` after a recorded trajectory
`τ` of `T = |τ|` iterations of Algorithm 2 (Claim 4.14, p.37: "with the description of Γ up to
iteration t, we can recursively algorithmically access X_t"), with the envelope `M_X` of that state;
`Δ[X_T] = H[X_T] + log M_X`. `Ω(1/polylog K)` is `c₀ / (log₂ (2K))^{c₁}` with `c₀ > 0`;
`T = O(log log K)` is `|τ| ≤ C (log₂ log₂ (4K) + 1)`; `O(log K)` is `C (log₂ K + 2)`. The main
program's resource bounds hold on every run (Claim 4.15: "it always uses"); the per-call bounds are
expectations over the call's own randomness (Claim 4.15: "expected sample complexity poly(K)"), for
every output description on the success event and every coin input `x`. -/
theorem theorem_4_2_ggmt_access :
    ∃ (P Psamp Pcoin : Program) (C c₀ : ℝ) (c c₁ : ℕ), 0 < c₀ ∧
      ∀ (n : ℕ) (A : Finset (Vec n)) (hA : A.Nonempty) (K : ℕ),
      ((A + A).card : ℝ) ≤ K * A.card →
      (∀ ω : Tape n, IsRunTape A ω →
        ∃ t, (run n P (memberRate A) [n, K] ω t).out.isSome ∧
          ((run n P (memberRate A) [n, K] ω t).samples : ℝ) ≤ C * (K : ℝ) ^ c ∧
          ((run n P (memberRate A) [n, K] ω t).queries : ℝ) ≤ C * (K : ℝ) ^ c ∧
          ((run n P (memberRate A) [n, K] ω t).cost : ℝ) ≤ C * ((n : ℝ) + 1) * (K : ℝ) ^ c) ∧
      ProbAtLeast (tapeMeasure (uniformLaw A hA))
        {ω | ∃ o, Outputs n P (memberRate A) [n, K] ω o ∧
          ∃ τ : List (Family × FamilyOutcome n),
            (τ.length : ℝ) ≤ C * (Real.logb 2 (Real.logb 2 (4 * K)) + 1) ∧
            (let s := τ.foldl (fun s e => nextState e.1 s e.2) (rootState A hA)
            IsAccess s.X s.MX ∧ slack s.X s.MX ≤ C ∧
            (∃ H : Submodule (ZMod 2) (Vec n), rd s.X.sample (subspaceLaw H) ≤ C) ∧
            rd (uniformLaw A hA) s.X.sample ≤ C * (Real.logb 2 K + 2) ∧
            (∀ y : Vec n, ProbAtLeast (tapeMeasure (uniformLaw A hA))
              {ω' | Outputs n Psamp (memberRate A) (n :: K :: o) ω' [encodeVec y]}
              (s.X.sample y).toReal) ∧
            (∀ (x : Vec n) (b : Bool), ProbAtLeast (tapeMeasure (uniformLaw A hA))
              {ω' | Outputs n Pcoin (memberRate A) (n :: K :: encodeVec x :: o) ω'
                [if b then 1 else 0]}
              ((s.X.coin x) b).toReal) ∧
            ExpectedWithin Psamp (memberRate A) (n :: K :: o) (tapeMeasure (uniformLaw A hA))
              (IsRunTape A) MState.samples (C * (K : ℝ) ^ c) ∧
            ExpectedWithin Psamp (memberRate A) (n :: K :: o) (tapeMeasure (uniformLaw A hA))
              (IsRunTape A) MState.queries (C * (K : ℝ) ^ c) ∧
            ExpectedWithin Psamp (memberRate A) (n :: K :: o) (tapeMeasure (uniformLaw A hA))
              (IsRunTape A) MState.cost (C * ((n : ℝ) + 1) * (K : ℝ) ^ c) ∧
            ∀ x : Vec n,
              ExpectedWithin Pcoin (memberRate A) (n :: K :: encodeVec x :: o)
                (tapeMeasure (uniformLaw A hA)) (IsRunTape A) MState.samples (C * (K : ℝ) ^ c) ∧
              ExpectedWithin Pcoin (memberRate A) (n :: K :: encodeVec x :: o)
                (tapeMeasure (uniformLaw A hA)) (IsRunTape A) MState.queries (C * (K : ℝ) ^ c) ∧
              ExpectedWithin Pcoin (memberRate A) (n :: K :: encodeVec x :: o)
                (tapeMeasure (uniformLaw A hA)) (IsRunTape A) MState.cost
                (C * ((n : ℝ) + 1) * (K : ℝ) ^ c))}
        (c₀ / Real.logb 2 (2 * K) ^ c₁) := by sorry

end Supplement

end AlgoPFR
