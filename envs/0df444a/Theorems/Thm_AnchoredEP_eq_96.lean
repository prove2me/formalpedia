-- Prove2me | Theorems.Thm_AnchoredEP_eq_96
-- name    : AnchoredEP.eq_96
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:43.759647+00:00
-- url     : https://prove2.me/theorems/13906e91-7a40-48c5-99a1-420b02ce698d
-- title:
--   Eq. (96) — growth of $A_k$ along accepted tensor steps
-- statement:
--   Consider Algorithm 3 with order $p\ge2$, $L_p>0$, $\varepsilon>0$, $v_0\in H(z_0)$ and $M_p=(p+1)L_p$, under the standing assumptions ($F$ monotone, $H$ maximal monotone, $z^\ast$ any solution of Problem (1)) and Assumption 5.1, with exact subproblem solutions. If the run reaches outer iteration $k\ge1$, its first $k$ outer iterations having ended with accepted bisection steps, then
--   $$
--   A_k\ \ge\ \frac{p!}{2^{(p+1)/2}\,p^{(3p-1)/2}}\cdot\frac{k^{(3p-1)/2}}{M_p\|z_0-z^\ast\|^{p-1}} .
--   $$
--   Together with Theorem 3.2 this gives the outer-iteration bound of Theorem 5.1.
--
--   Differences from the source:
--   - encoding: the (p−1)th derivative of F exists and is L_p-Lipschitz (Assumption 5.1) → Assumption51 p L F = ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv (p−1) F z − iteratedFDeriv (p−1) F z′‖ ≤ L‖z − z′‖; reason: the existence of D^{p−1}F is presupposed by the source; a Lipschitz (p−1)th derivative is continuous, so the same operators qualify
--   - encoding: outer iteration k of Algorithm 3 (exact subproblem solutions) → a state s with tensorRun F p L ε sol z0 v0 k = .running s, for every solver sol with IsSubSolver; reason: Algorithm 3 as a deterministic run with its subproblem oracle as a parameter; the solution of (87) is unique, so every admissible solver gives the source's run
--   - encoding: the first k outer iterations ended with accepted steps → tensorRun … k = .running s and every earlier line search returns (hypothesis on LineSearchReturnsWithin); reason: a running state at index k means no earlier return; the hypothesis only excludes the placeholder branch of stepSize, which never occurs
--   - encoding: A_k ≥ X/(M_p‖z₀ − z∗‖^{p−1}) → A_k · M_p‖z₀ − z∗‖^{p−1} ≥ X; reason: equivalent when z₀ ≠ z∗; avoids division by zero at z₀ = z∗, where the run returns in its first iteration and no state with k ≥ 1 is reached
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.3, proof of Theorem 5.1, Eq. (96), p.39

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_AnchoredEP_IsSolution
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_IsSubSolver
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_LineSearchReturnsWithin
import Definitions.Def_AnchoredEP_RunState
import Definitions.Def_AnchoredEP_tensorRun

open ThreeOpSplitting.Convergence

namespace AnchoredEP

/-- **Eq. (96): growth of `A_k` along accepted tensor steps.** Jiang–Yoon, arXiv:2609.30212,
Appendix G.3, proof of Theorem 5.1 (outer iteration bound), Eq. (96), p.39: "Applying Lemma E.1
with `α = p/(p − 1)` gives `B_k ≥ (ck/p)^{p−1}`. Consequently,
`A_k = B_k^{(3p−1)/(2(p−1))} ≥ p!/(2^{(p+1)/2} p^{(3p−1)/2}) · k^{(3p−1)/2}/(M_p‖z₀ − z∗‖^{p−1})`."

Setting: Algorithm 3 with order `p ≥ 2`, `L_p > 0`, `ε > 0`, `v₀ ∈ H(z₀)`, `M_p = (p + 1)L_p`,
under the standing assumptions (`F` monotone, `H` maximal monotone, `z∗` any solution of
Problem (1)) and Assumption 5.1, with any exact subproblem solver. If the run reaches the start of
outer iteration `k ≥ 1` — so the first `k` outer iterations ended with steps accepted by the
bisection (p.38: "the line search returns `T` accepted steps") — then (96) holds, written
multiplied out:
`A_k · M_p‖z₀ − z∗‖^{p−1} ≥ p!/(2^{(p+1)/2} p^{(3p−1)/2}) · k^{(3p−1)/2}`.

**Formalization Note.** `tensorRun … k = .running s` with `s.A = A_k`. The hypothesis `hacc`
says that every line search performed before iteration `k` returned (the source's "accepted
steps"); it only excludes the placeholder branch of `stepSize`. The exponents `(p+1)/2` and
`(3p−1)/2` are real (`Real.rpow`). -/
theorem eq_96 {d : ℕ} (p : ℕ) (hp : 2 ≤ p) (L ε : ℝ)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin d)))))
    (hH : IsMaximalMonotone H)
    (zstar : EuclideanSpace ℝ (Fin d)) (hstar : IsSolution F H zstar)
    (hA : Assumption51 p L F) (hL : 0 < L) (hε : 0 < ε)
    (z0 v0 : EuclideanSpace ℝ (Fin d)) (hv0 : v0 ∈ H z0)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsol : IsSubSolver F H p L sol)
    (k : ℕ) (hk1 : 1 ≤ k) (s : IterState d) (hk : tensorRun F p L ε sol z0 v0 k = .running s)
    (hacc : ∀ i < k, ∀ s' : IterState d, tensorRun F p L ε sol z0 v0 i = .running s' →
      ε < ‖F s'.z + s'.v‖ → ∃ n : ℕ, LineSearchReturnsWithin F p L ε sol z0 s' n) :
    (p.factorial : ℝ) / (2 ^ (((p : ℝ) + 1) / 2) * (p : ℝ) ^ ((3 * (p : ℝ) - 1) / 2)) *
        (k : ℝ) ^ ((3 * (p : ℝ) - 1) / 2) ≤
      s.A * (((p : ℝ) + 1) * L * ‖z0 - zstar‖ ^ (p - 1)) := by sorry

end AnchoredEP
