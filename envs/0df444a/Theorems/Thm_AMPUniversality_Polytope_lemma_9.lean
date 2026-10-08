-- Prove2me | Theorems.Thm_AMPUniversality_Polytope_lemma_9
-- name    : AMPUniversality.Polytope.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:49.342961+00:00
-- url     : https://prove2.me/theorems/c7628e3d-07f6-438b-a6e3-e9eff72ecca0
-- title:
--   Lemma 9, p. 61 — scalar characterization on both sides of the phase boundary
-- statement:
--   Let $0<\delta,\rho<1$, put $\varepsilon=\rho\delta$, and choose the positive $\alpha$ for which $f_\delta(\alpha)=\delta$. The function $G_\varepsilon$ attains its minimum at a positive $\beta$, and
--
--   $$\rho>f_\rho(\alpha)\iff\delta<G_\varepsilon(\beta),\qquad\rho<f_\rho(\alpha)\iff\delta>G_\varepsilon(\beta).$$
--
--   This translates both sides of the geometric phase boundary into inequalities for the scalar state-evolution minimum. **Formalization Note** The page's $\varepsilon$ is the nonzero-entry probability $\rho\delta$; the result is stated in the interior regime $\varepsilon\in(0,1)$.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 61, Lemma 9 and equation (C.9)

import Mathlib
import Definitions.Def_AMPUniversality_Polytope_Curve
import Definitions.Def_AMPUniversality_Polytope_GEps

set_option autoImplicit false
open MeasureTheory Set

namespace AMPUniversality.Polytope

/-- Lemma 9, p. 61: both sides of the phase boundary are characterized by
the minimum of the scalar state-evolution function. -/
theorem lemma_9 (δ ρ α : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hα : 0 < α) (hcurve : fδ α = δ) :
    ∃ β : ℝ,
      0 < β ∧
      (∀ γ : ℝ, 0 < γ → GEps (ρ * δ) β ≤ GEps (ρ * δ) γ) ∧
      (ρ > fρ α ↔ δ < GEps (ρ * δ) β) ∧
      (ρ < fρ α ↔ δ > GEps (ρ * δ) β) := by sorry

end AMPUniversality.Polytope
