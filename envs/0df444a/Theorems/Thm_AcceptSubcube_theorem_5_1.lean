-- Prove2me | Theorems.Thm_AcceptSubcube_theorem_5_1
-- name    : AcceptSubcube.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:16.112743+00:00
-- url     : https://prove2.me/theorems/ef3322c8-6871-4e29-ab6c-1da6d216db32
-- title:
--   Theorem 5.1 — the pinning hierarchy
-- statement:
--   Fix $k\ge2$. There are $A_k>0$ and $C_k$ such that for every $0\le t\le k-2$, with $\ell=k-t$ and $\Pi_t=\binom nt$, on complete Boolean $k$-CSPs with nontrivial predicates and property $\mathsf P_t$:
--
--   1. a randomized polynomial-time algorithm that is not given $B=\mathrm{OPT}$ outputs, for every rational $0<\zeta<1/2$ and with probability at least $1-\zeta$, an assignment $Y$ with
--   $$\frac{C_{\mathcal I}(Y)}B\le\begin{cases}A_k,&\ell=2,\\ A_k\sqrt{\log(2+B/\Pi_t)},&\ell=3,\\ A_k\big(n/\log(n+2)\big)^{\ell-3},&\ell\ge4,\end{cases}\qquad(B>0);$$
--   2. (a) all assignments of cost at most a given integer $B_0$ are enumerated deterministically within $(n+2)^{\lceil C_k(1+(B_0/\Pi_t)^{1/\ell})\rceil}$ steps, and for every fixed $c>0$ a deterministic polynomial-time algorithm finds an optimum whenever $B\le c\Pi_t$;
--   3. (b) for fixed $c>0$ and $0<\delta\le1$ a randomized polynomial-time algorithm outputs, with probability at least $1-\zeta$, an assignment of cost at most $(1+\delta)B$ whenever $B\le c\,\Pi_t\log^\ell(n+2)$.
--
--   Theorem 1.1 is the case $t=k-h-1$, $\zeta=(n+2)^{-10}$.
--
--   Differences from the source:
--   - reading: a randomized algorithm … in worst-case time n^{O_k(1)} poly(log(1/ζ)) → a TM2 polynomial-time machine on ((I, ζ), coins), ζ rational in binary, coins of length p(|(I, ζ)|), probability = exact fraction of coin strings; reason: the paper names no machine model; the input length is n^{O_k(1)} plus the bits of ζ, which a machine must read
--   - reading: (a) enumerated deterministically in time n^{O_k(1+(B₀/Π_t)^{1/ℓ})} → one TM2 machine on (I, B₀) halting within (n+2)^{⌈C_k(1+(B₀/Π_t)^{1/ℓ})⌉} steps, output a duplicate-free list of exactly the assignments of cost ≤ B₀; reason: base n + 2 covers small n; C_k chosen after k (t ranges over a finite set)
--   - reading: (b) a randomized polynomial-time (1 + δ)-approximation → with probability at least 1 − ζ for every rational ζ ∈ (0, 1/2), ζ an input; reason: the amplification paragraph (p.28) proves all of Theorem 5.1 with ζ; this is the stronger reading
--   - reading: A_k depends only on k → A_k chosen after k and before t; reason: literal
--   - encoding: complete Boolean k-CSPs → IsComplete k ∧ Nontrivial on the raw instance type; reason: the §2 standing assumption (p.9) that every predicate is nontrivial
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 5.1, p.25

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_subcubeDim
import Definitions.Def_AcceptSubcube_encInst
import Definitions.Def_AcceptSubcube_coinFrac
import Definitions.Def_AcceptSubcube_ratio11

namespace AcceptSubcube

/-- **Theorem 5.1 (Pinning hierarchy).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 5.1, p.25: "Fix k ≥ 2 and
0 ≤ t ≤ k − 2, and let ℓ = k − t. On complete Boolean k-CSPs with P_t, a randomized algorithm that
is not given B outputs, for any 0 < ζ < 1/2 and with probability at least 1 − ζ, an assignment Y
with C_I(Y)/B ≤ A_k (ℓ = 2), A_k √log(2 + B/Π_t) (ℓ = 3), A_k (n/log(n + 2))^{ℓ−3} (ℓ ≥ 4)
(B > 0), (22) where A_k depends only on k, in worst-case time n^{O_k(1)} poly(log(1/ζ)). Moreover:
(a) all assignments of cost at most a given integer B₀ can be enumerated deterministically in time
n^{O_k(1+(B₀/Π_t)^{1/ℓ})}; in particular OPT is found exactly, deterministically and in polynomial
time, when B ≤ c Π_t for a fixed c; (b) for fixed c > 0 and 0 < δ ≤ 1 there is a randomized
polynomial-time (1 + δ)-approximation when B ≤ c Π_t log^ℓ(n + 2), with exponent depending on
k, c, δ only."

For every `k ≥ 2` there are `A_k > 0` and `C_k` such that for every `0 ≤ t ≤ k − 2`:
1. a polynomial-time machine on (instance, `ζ`, coins) whose output satisfies (22) for at least a
   `1 − ζ` fraction of the coin strings, on every instance of the class with `B > 0` and every
   rational `0 < ζ < 1/2` (it is not given `B`);
2. (a) a deterministic enumerator of exactly the assignments of cost `≤ B₀`, halting within
   `(n + 2)^{⌈C_k (1 + (B₀/Π_t)^{1/ℓ})⌉}` steps, and, for every `c > 0`, a deterministic
   polynomial-time machine returning an optimum whenever `B ≤ c Π_t`;
3. (b) for every `c > 0` and `0 < δ ≤ 1`, a polynomial-time machine on (instance, `ζ`, coins)
   whose output costs at most `(1 + δ)B` for at least a `1 − ζ` fraction of the coin strings,
   whenever `B ≤ c Π_t log^ℓ(n + 2)` and `0 < ζ < 1/2`.

**Formalization Note.** The class: complete Boolean `k`-CSPs with nontrivial predicates (§2
standing assumption, p.9) having `P_t`. A randomized algorithm is a TM2 machine reading the instance,
`ζ` (a rational in binary) and a coin string of length `p(|(I, ζ)|)` for a polynomial `p` fixed
before the input; the probability is the exact fraction of coin strings. "Worst-case time
n^{O_k(1)} poly(log(1/ζ))" is read as time polynomial in the input length (which is `n^{O_k(1)}`
plus the bit length of `ζ`). (b) is read with the same `1 − ζ` guarantee as the main clause (the
amplification paragraph of p.28 proves all of Theorem 5.1 with `ζ`). Natural logarithms (p.9). -/
theorem theorem_5_1 (k : ℕ) (hk : 2 ≤ k) :
    ∃ (A : ℝ) (Ca : ℝ), 0 < A ∧ ∀ t : ℕ, t ≤ k - 2 →
      (∃ (p : Polynomial ℕ) (alg : (GInst × ℚ) × List Bool → List Bool),
        Nonempty (Turing.TM2ComputableInPolyTime encInstRatCoins encAssign alg) ∧
        ∀ I : GInst, I.IsComplete k → I.Nontrivial → InstPt t I → 0 < OPT I →
          ∀ ζ : ℚ, 0 < ζ → ζ < 1 / 2 →
            1 - (ζ : ℝ) ≤
              coinFrac (p.eval (encInstRat (I, ζ)).length) (fun w =>
                (cost I (asg I (alg ((I, ζ), w))) : ℝ) ≤ ratio51 k t A I * (OPT I : ℝ))) ∧
      (∃ enum : GInst × ℕ → List (List Bool),
        ComputesWithinOn (fun x : GInst × ℕ => x.1.IsComplete k ∧ x.1.Nontrivial ∧ InstPt t x.1)
          encInstNat encAssignList enum
          (fun x => (x.1.n + 2) ^
            ⌈Ca * (1 + ((x.2 : ℝ) / (x.1.n.choose t : ℝ)) ^ ((1 : ℝ) / ((k - t : ℕ) : ℝ)))⌉₊) ∧
        ∀ I : GInst, I.IsComplete k → I.Nontrivial → InstPt t I → ∀ B₀ : ℕ,
          (enum (I, B₀)).Nodup ∧ (∀ y ∈ enum (I, B₀), y.length = I.n) ∧
          ∀ x : Fin I.n → Bool, List.ofFn x ∈ enum (I, B₀) ↔ cost I x ≤ B₀) ∧
      (∀ c : ℝ, 0 < c → ∃ opt : GInst → List Bool,
        Nonempty (Turing.TM2ComputableInPolyTime encInst encAssign opt) ∧
        ∀ I : GInst, I.IsComplete k → I.Nontrivial → InstPt t I →
          (OPT I : ℝ) ≤ c * (I.n.choose t : ℝ) → cost I (asg I (opt I)) = OPT I) ∧
      (∀ c δ : ℝ, 0 < c → 0 < δ → δ ≤ 1 →
        ∃ (p : Polynomial ℕ) (alg : (GInst × ℚ) × List Bool → List Bool),
          Nonempty (Turing.TM2ComputableInPolyTime encInstRatCoins encAssign alg) ∧
          ∀ I : GInst, I.IsComplete k → I.Nontrivial → InstPt t I →
            (OPT I : ℝ) ≤ c * (I.n.choose t : ℝ) * Real.log ((I.n : ℝ) + 2) ^ (k - t) →
            ∀ ζ : ℚ, 0 < ζ → ζ < 1 / 2 →
              1 - (ζ : ℝ) ≤
                coinFrac (p.eval (encInstRat (I, ζ)).length) (fun w =>
                  (cost I (asg I (alg ((I, ζ), w))) : ℝ) ≤ (1 + δ) * (OPT I : ℝ))) := by sorry

end AcceptSubcube
