-- Prove2me | Theorems.Thm_ExtrapBias_Beliefs_scaled_focs
-- name    : ExtrapBias.Beliefs.scaled_focs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:04.62119+00:00
-- url     : https://prove2.me/theorems/d2be026a-a311-4d7d-a681-e5e2ee585372
-- title:
--   Equations (26)–(27), pp. 17–18 — scaled investment and worst-case beliefs
-- statement:
--   At cash ratio m, write F₁=F′(m). Assume F₁>0 and F(m)−mF₁>0. The unique maximizing investment and unique minimizing angle of the scaled HJB bracket (25) are
--   $$
--   i(m)=\frac{F(m)-F_1(m+1)}{\theta F_1},
--   \qquad
--   \phi(m)=\arctan\!\left(\frac{F_1}{F(m)-mF_1}
--   \frac{\sigma_Y\kappa_T}{\sigma_\delta\kappa_P}\right)\in(0,\pi/2).
--   $$
--   The associated distortions hᴾ(m)=−κP cos φ(m) and hᵀ(m)=−κT sin φ(m) lie on the ambiguity ellipse’s boundary.
--
--   This supplies the pointwise optimizer used by the model’s worst-case beliefs.
--
--   **Formalization Note** Positivity of F₁ and F−mF₁ is stated at this pointwise level to keep both divisions meaningful. In the main theorem these inequalities follow from the scaled value system and positive liquidation value.
-- source:
--   Lee & Rivera, Extrapolation Bias and Dynamic Liquidity Management, working paper (May 24, 2019), pp. 17–18, (25)–(27)

import Mathlib
import Definitions.Def_ExtrapBias_Beliefs_Model

namespace ExtrapBias.Beliefs

/-- Equations (26)–(27), pp. 17–18: the scaled investment and
worst-case angle are the unique optimizers of (25). -/
theorem scaled_focs (p : Params) (F : ℝ → ℝ) (m : ℝ)
    (hF1 : 0 < deriv F m) (hA : 0 < F m - deriv F m * m) :
    phiOpt p F m ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧
    (∀ φ : ℝ, ∀ i : ℝ,
      bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i φ ≤
        bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m (iOpt p F m) φ ∧
      (bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i φ =
        bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m (iOpt p F m) φ →
        i = iOpt p F m)) ∧
    (∀ i : ℝ, ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i (phiOpt p F m) ≤
        bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i φ ∧
      (bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i φ =
        bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i (phiOpt p F m) →
        φ = phiOpt p F m)) ∧
    (hP p F m / p.kapP) ^ 2 + (hT p F m / p.kapT) ^ 2 = 1 := by sorry

end ExtrapBias.Beliefs
