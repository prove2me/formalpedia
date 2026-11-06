-- Prove2me | Theorems.Thm_AnchoredEP_lemma_H_4
-- name    : AnchoredEP.lemma_H_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:47.785853+00:00
-- url     : https://prove2.me/theorems/246ae08e-034c-424c-9893-ed496159982f
-- title:
--   Lemma H.4 — changing the center of the regularized Taylor model
-- statement:
--   For every order $p\ge2$ there is a constant $C_p>0$, depending only on $p$, with the following property. Let $F:\mathbb R^d\to\mathbb R^d$ be monotone and satisfy Assumption 5.1 with $L_p>0$, and let $M_p=(p+1)L_p$. Then for all $y,y',w\in\mathbb R^d$,
--   $$
--   \big\|\mathbb T^{(p-1)}_{L_p}(w;y)-\mathbb T^{(p-1)}_{L_p}(w;y')\big\|\le C_pM_p\,\|y-y'\|\,\big(\|w-y\|+\|y-y'\|\big)^{p-1} .
--   $$
--   It controls how the subproblem of the line search moves when the trial step, and with it the Taylor center, changes.
--
--   Differences from the source:
--   - encoding: the (p−1)th derivative of F exists and is L_p-Lipschitz (Assumption 5.1) → Assumption51 p L F = ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv (p−1) F z − iteratedFDeriv (p−1) F z′‖ ≤ L‖z − z′‖; reason: the existence of D^{p−1}F is presupposed by the source; a Lipschitz (p−1)th derivative is continuous, so the same operators qualify
--   - encoding: a constant C_p > 0 depending only on p → ∃ C > 0 quantified after p and before the dimension and all data; reason: the source's O_p / C_p convention
--   - generalization: the paper's standing assumptions on H and the solvability of Problem (1) → not assumed; reason: the lemma concerns F and its model only; with them added it is the source's statement
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Lemma H.4, p.43, Eq. (107)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_regTaylor

open ThreeOpSplitting.Convergence

namespace AnchoredEP

/-- **Lemma H.4 (changing the center of the regularized model).** Jiang–Yoon, arXiv:2609.30212,
Lemma H.4, Eq. (107), p.43: "For `y, y′, w ∈ ℝ^d`, there is a constant `C_p > 0`, depending only on
`p`, such that `‖𝕋_λ^{(p−1)}(w; y) − 𝕋_λ^{(p−1)}(w; y′)‖ ≤ C_p M_p‖y − y′‖(‖w − y‖ + ‖y − y′‖)^{p−1}`."
Here `λ = L_p` and `M_p = (p + 1)L_p` (Appendix G.2, p.37), under Assumption 5.1.

For each order `p ≥ 2` there is one `C_p > 0` that works for every dimension `d`, every monotone
`F` satisfying Assumption 5.1 with `L_p > 0`, and all `y, y′, w`.

**Formalization Note.** `regTaylor F p L y w` is `𝕋_{L_p}^{(p−1)}(w; y)` (center `y`). The constant
is quantified before the dimension and the data, so it depends on `p` only. -/
theorem lemma_H_4 (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (L : ℝ) (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin d)))) →
      Assumption51 p L F → 0 < L →
      ∀ y y' w : EuclideanSpace ℝ (Fin d),
        ‖regTaylor F p L y w - regTaylor F p L y' w‖ ≤
          C * (((p : ℝ) + 1) * L) * ‖y - y'‖ * (‖w - y‖ + ‖y - y'‖) ^ (p - 1) := by sorry

end AnchoredEP
