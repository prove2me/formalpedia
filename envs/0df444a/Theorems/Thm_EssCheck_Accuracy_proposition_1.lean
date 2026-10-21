-- Prove2me | Theorems.Thm_EssCheck_Accuracy_proposition_1
-- name    : EssCheck.Accuracy.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:11.654195+00:00
-- url     : https://prove2.me/theorems/4403aeba-01ce-4d9c-b850-1c1a8814a3bc
-- title:
--   Proposition 1 — a marginal accuracy increase weakly reduces welfare without an effective royalty cap
-- statement:
--   Suppose the royalty cap is ineffective, $\bar\alpha=1$. Fix accuracy $\beta_0\in[0,1)$ and an interior equilibrium research effort $x^*(\beta_0)$ with no hybrid–pooling boundary in any state of positive probability. Along a right-continuous path of nearby equilibrium efforts, the right derivative of welfare exists and satisfies
--   $$\frac{d}{d\beta}w\bigl(\beta,x^*(\beta)\bigr)\bigg|_{\beta_0+}\le0.$$
--   Thus a marginal increase in the accuracy of essentiality checks weakly reduces welfare in the paper's model.
--
--   **Formalization Note** The path uses the private first-order condition at and near $\beta_0$ and does not assume its derivative. The path's right continuity and $c''(x^*(\beta_0))>0$ state premises of the paper's local comparative-statics argument. Strictness is required only for states that occur with positive probability. The weak inequality follows the paper's proof and permits a zero derivative in a pooling corner.
-- source:
--   Schuett & Wipusanawan, Essentiality Checks for Standard Essential Patents, TILEC Discussion Paper DP 2023-21 (Dec. 2023; SSRN 4688864), p. 24 (PDF 25), Proposition 1; p. 25 (PDF 26), concluding derivative inequality

import Mathlib
import Definitions.Def_EssCheck_Accuracy_Model

namespace EssCheck.Accuracy

theorem proposition_1 {n : ℕ} (M : Model n) (hS : M.Standing)
    (hα : M.αbar = 1) (β0 : ℝ) (hβ0 : 0 ≤ β0) (hβ1 : β0 < 1)
    (xs : ℝ → ℝ)
    (heq : ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), IsEqEffort M β (xs β))
    (heq0 : IsEqEffort M β0 (xs β0))
    (hcont : ContinuousWithinAt xs (Set.Ici β0) β0)
    (hstrict : ∀ i, (0 < M.pH i ∨ 0 < M.p0 i) → ¬ Eq4 M β0 (xs β0) i)
    (hc2 : 0 < iteratedDeriv 2 M.c (xs β0)) :
    ∃ d : ℝ,
      HasDerivWithinAt (fun β => welfare M β (xs β)) d (Set.Ici β0) β0 ∧
      d ≤ 0 := by sorry

end EssCheck.Accuracy
