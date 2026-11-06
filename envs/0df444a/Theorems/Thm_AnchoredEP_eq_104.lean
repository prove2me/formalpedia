-- Prove2me | Theorems.Thm_AnchoredEP_eq_104
-- name    : AnchoredEP.eq_104
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:49.429779+00:00
-- url     : https://prove2.me/theorems/e6711756-2d3c-439e-b6b3-2c5994a8ac63
-- title:
--   Eq. (104) — uniform trajectory bounds for the tensor run
-- statement:
--   Consider Algorithm 3 with order $p\ge2$, $L_p>0$, $\varepsilon>0$ and $v_0\in H(z_0)$, under the standing assumptions ($F$ monotone, $H$ maximal monotone, $z^\ast$ any solution of Problem (1)) and Assumption 5.1, with exact subproblem solutions. Every outer iterate $z_k$ generated before termination satisfies, with $g_k=F(z_k)+v_k$,
--   $$
--   \|z_0-z_k-A_kg_k\|\le3\|z_0-z^\ast\|,\qquad \|z_k-z_0\|\le3\|z_0-z^\ast\| .
--   $$
--   These bounds keep the trial displacements of the line search under control.
--
--   Differences from the source:
--   - encoding: the (p−1)th derivative of F exists and is L_p-Lipschitz (Assumption 5.1) → Assumption51 p L F = ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv (p−1) F z − iteratedFDeriv (p−1) F z′‖ ≤ L‖z − z′‖; reason: the existence of D^{p−1}F is presupposed by the source; a Lipschitz (p−1)th derivative is continuous, so the same operators qualify
--   - encoding: outer iteration k of Algorithm 3 (exact subproblem solutions) → a state s with tensorRun F p L ε sol z0 v0 k = .running s, for every solver sol with IsSubSolver; reason: Algorithm 3 as a deterministic run with its subproblem oracle as a parameter; the solution of (87) is unique, so every admissible solver gives the source's run
--   - encoding: the first k outer iterations ended with accepted steps → tensorRun … k = .running s and every earlier line search returns (hypothesis on LineSearchReturnsWithin); reason: a running state at index k means no earlier return; the hypothesis only excludes the placeholder branch of stepSize, which never occurs
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix H.1, Eq. (104), p.42

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

/-- **Eq. (104): uniform trajectory bounds for the tensor run.** Jiang–Yoon, arXiv:2609.30212,
Appendix H.1, Eq. (104), p.42: "Thus the accepted iterates form an AEP trajectory with `ρ = 1/√2`,
and the same proof as that of Lemma F.2 gives `‖z₀ − z_k − A_k g_k‖ ≤ 3‖z₀ − z∗‖`,
`‖z_k − z₀‖ ≤ 3‖z₀ − z∗‖`", where `g_k := F(z_k) + v_k`; Lemma F.2 (p.31) is stated for "every
outer iterate generated before termination".

Setting: Algorithm 3 with order `p ≥ 2`, `L_p > 0`, `ε > 0`, `v₀ ∈ H(z₀)`, under the standing
assumptions (`F` monotone, `H` maximal monotone, `z∗` any solution of Problem (1)) and
Assumption 5.1, with any exact subproblem solver. For every outer iterate `z_k` the run reaches,
both bounds hold.

**Formalization Note.** `tensorRun … k = .running s` with `s = (z_k, v_k, A_k)`. The hypothesis
`hacc` says that every line search performed before iteration `k` returned (the "accepted
iterates" of the source); it only excludes the placeholder branch of `stepSize`. -/
theorem eq_104 {d : ℕ} (p : ℕ) (hp : 2 ≤ p) (L ε : ℝ)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin d)))))
    (hH : IsMaximalMonotone H)
    (zstar : EuclideanSpace ℝ (Fin d)) (hstar : IsSolution F H zstar)
    (hA : Assumption51 p L F) (hL : 0 < L) (hε : 0 < ε)
    (z0 v0 : EuclideanSpace ℝ (Fin d)) (hv0 : v0 ∈ H z0)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsol : IsSubSolver F H p L sol)
    (k : ℕ) (s : IterState d) (hk : tensorRun F p L ε sol z0 v0 k = .running s)
    (hacc : ∀ i < k, ∀ s' : IterState d, tensorRun F p L ε sol z0 v0 i = .running s' →
      ε < ‖F s'.z + s'.v‖ → ∃ n : ℕ, LineSearchReturnsWithin F p L ε sol z0 s' n) :
    ‖z0 - s.z - s.A • (F s.z + s.v)‖ ≤ 3 * ‖z0 - zstar‖ ∧ ‖s.z - z0‖ ≤ 3 * ‖z0 - zstar‖ := by sorry

end AnchoredEP
