-- Prove2me | Theorems.Thm_CrowdContest_Pooling_eq_A_6
-- name    : CrowdContest.Pooling.eq_A_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:22.791733+00:00
-- url     : https://prove2.me/theorems/50f75cac-8c14-4ee6-bcd3-be0df8cc60b9
-- title:
--   (A.6), proof of Proposition 1, OA pp. 2–3 — at a joint equilibrium, C₁′(s₁) = C₂′(s₂) = A h°(ξ°;n)
-- statement:
--   In the setting of Lemma 3, let $(s_1,s_2)$ with $s_1,s_2>0$ be a symmetric equilibrium of the joint contest with grand prize $A$ and costs $C_1,C_2$. Then the marginal cost of each attribute equals the prize times $h^\circ$:
--   $$C_1'(s_1)=A\,h^\circ(\xi^\circ;n)\qquad\text{and}\qquad C_2'(s_2)=A\,h^\circ(\xi^\circ;n).$$
--   Equivalently, $e^{\circ*}=s_1+s_2=C_1'^{-1}(Ah^\circ(\xi^\circ;n))+C_2'^{-1}(Ah^\circ(\xi^\circ;n))$, the equality used in display (A.6) to write $\Delta^e_n$ as a difference of inverse marginal costs.
--
--   Combined with Lemma 1 for the two sub-contests, it reduces the comparison of equilibrium efforts to comparing $wAh$, $(1-w)Ah$ and $Ah^\circ$ under the increasing maps $C_l'^{-1}$.
--
--   **Formalization Note** The inverse marginal costs of the page are replaced by the equivalent derivative identities. Interior equilibrium efforts are assumed.
-- source:
--   Hu & Wang, Joint vs. Separate Crowdsourcing Contests, authors' accepted manuscript (TSpace; SSRN 2892683; Manag. Sci. doi:10.1287/mnsc.2020.3683), proof of Proposition 1, display (A.6), OA pp. 2–3

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

open MeasureTheory

namespace CrowdContest.Pooling

/-- (A.6), proof of Proposition 1, OA pp. 2–3: at a symmetric equilibrium `(s₁, s₂)` of the joint
contest with interior efforts, each attribute's marginal cost equals `A h°(ξ°; n)`:
`C₁'(s₁) = C₂'(s₂) = A h°(ξ°; n)`, so that
`e°* = s₁ + s₂ = C₁'⁻¹(A h°(ξ°; n)) + C₂'⁻¹(A h°(ξ°; n))`. -/
theorem eq_A_6 (n : ℕ) (hn : 2 ≤ n) (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ)
    (A : ℝ) (C₁ C₂ : ℝ → ℝ) (hC₁ : IsCost C₁) (hC₂ : IsCost C₂) (s₁ s₂ : ℝ)
    (hs : IsSymEqJoint ψ n A C₁ C₂ s₁ s₂) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    deriv C₁ s₁ = A * hFun (convDensity ψ) n ∧ deriv C₂ s₂ = A * hFun (convDensity ψ) n := by sorry

end CrowdContest.Pooling
