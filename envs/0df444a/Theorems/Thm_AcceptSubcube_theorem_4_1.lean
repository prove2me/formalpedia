-- Prove2me | Theorems.Thm_AcceptSubcube_theorem_4_1
-- name    : AcceptSubcube.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:18.394235+00:00
-- url     : https://prove2.me/theorems/d70a24ba-494a-4c90-81b5-07c790ddc637
-- title:
--   Theorem 4.1 — SDP-strengthened Hamming-ball repair: $C_{\mathcal I}(\hat x)\le\alpha_k\sqrt{\log(r+2)}\,\mathrm{OPT}_{\tau,r}+K_kD_3(n)r^3$
-- statement:
--   There is an absolute constant $C$ such that for every fixed $k\ge3$ there are constants $\alpha_k$, $K_k$, $c_k$ and a randomized procedure running in time $c_k(n+2)^{Ck}$ which, given a $k$-uniform instance $\mathcal I$ with at most one unweighted predicate per $k$-set, a center $\tau$ and $1\le r\le n$, outputs with probability at least $3/4$ an assignment $\hat x$ with
--   $$C_{\mathcal I}(\hat x)\le\alpha_k\sqrt{\log(r+2)}\;\mathrm{OPT}_{\tau,r}+K_kD_3(n)\,r^3 .$$
--
--   The output need not lie in the ball. This is the cubic repair used when the residual arity is at least $3$.
--
--   Differences from the source:
--   - reading: a randomized n^{O(k)}-time procedure → one TM2 machine per k halting within c_k (n+2)^{C·k} steps (C absolute) on (I, τ, r, coins), coins of length p(|(I, τ, r)|), probability = exact fraction of coin strings; reason: the paper names no machine model; n + 2 covers small n
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 4.1, p.15

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_encInst
import Definitions.Def_AcceptSubcube_coinFrac

namespace AcceptSubcube

/-- **Theorem 4.1 (SDP-strengthened Hamming-ball repair).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 4.1, p.15: "For fixed k ≥ 3, an
instance with at most one unweighted predicate per k-set, a center τ, and 1 ≤ r ≤ n, a randomized
n^{O(k)}-time procedure outputs, with probability at least 3/4, an assignment x̂ with
C_I(x̂) ≤ α_k √log(r + 2) OPT_{τ,r} + K_k D₃(n) r³. (7) The output need not lie in the ball."

There is an absolute `C` and, for every `k ≥ 3`, constants `α_k`, `K_k`, `c_k`, a coin length
polynomial `p` and a machine on `((I, τ, r), coins)` that halts within `c_k (n + 2)^{C k}` steps and
whose output satisfies (7) for at least `3/4` of the coin strings of length `p(|(I, τ, r)|)`.

**Formalization Note.** `n^{O(k)}` is read as `c_k (n + 2)^{C·k}` with `C` absolute (chosen before
`k`). §4's setting: arbitrary well-formed `k`-uniform instance with at most one predicate per scope;
`τ` a list of `n` bits. The probability is the exact fraction of coin strings. -/
theorem theorem_4_1 :
    ∃ C : ℕ, ∀ k : ℕ, 3 ≤ k →
      ∃ (α K : ℝ) (c : ℕ) (p : Polynomial ℕ) (alg : (GInst × List Bool × ℕ) × List Bool → List Bool),
        ComputesWithinOn
          (fun y : (GInst × List Bool × ℕ) × List Bool =>
            y.1.1.WellFormed ∧ y.1.1.Uniform k ∧ y.1.1.ScopeUnique ∧ y.1.2.1.length = y.1.1.n ∧
              1 ≤ y.1.2.2 ∧ y.1.2.2 ≤ y.1.1.n ∧ y.2.length = p.eval (encBall y.1).length)
          encBallCoins encAssign alg (fun y => c * (y.1.1.n + 2) ^ (C * k)) ∧
        ∀ I : GInst, I.WellFormed → I.Uniform k → I.ScopeUnique →
          ∀ τ : Fin I.n → Bool, ∀ r : ℕ, 1 ≤ r → r ≤ I.n →
            (3 : ℝ) / 4 ≤
              coinFrac (p.eval (encBall (I, List.ofFn τ, r)).length) (fun w =>
                (cost I (asg I (alg ((I, List.ofFn τ, r), w))) : ℝ) ≤
                  α * Real.sqrt (Real.log ((r : ℝ) + 2)) * (OPTball I τ r : ℝ) +
                    K * (Dj k 3 I.n : ℝ) * (r : ℝ) ^ 3) := by sorry

end AcceptSubcube
