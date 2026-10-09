-- Prove2me | Theorems.Thm_ActuarialValuation_mortalityInnovation_Hattendorff_fundamental
-- name    : ActuarialValuation.mortalityInnovation_Hattendorff_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:28:49.064279+00:00
-- url     : https://prove2.me/theorems/7a61e024-f7ac-4ae1-9b9f-84192550049d
-- title:
--   Discrete mortality innovation orthogonality and variance capstone
-- statement:
--   The fundamental fully discrete finite-scenario theorem combines *derived* zero cross-year moments with the conditional-survival-factor variance allocation.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[I_iI_j]=0\ (i\ne j),\quad\operatorname{Var}(Z_n)=\sum_{t<n}\rho_t^2D_tp_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteMortalityInnovation
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
import Definitions.Def_actuarial_finiteMortalityVariance
open MeasureTheory

namespace ActuarialValuation

theorem mortalityInnovation_Hattendorff_fundamental {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (ρ : ℕ → ℝ) (n : ℕ) (hw : ∀ ω, 0 ≤ w ω)
  (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
  :
  ((∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, i < j →
      (∑ ω : Ω, w ω * finiteMortalityInnovation w K i ω *
        finiteMortalityInnovation w K j ω) = 0)
  ∧ (finiteMortalityVariance w (finiteMortalityDiscountedShock w K ρ n) =
      ∑ t ∈ Finset.range n, (ρ t) ^ 2 *
        finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t)) := by sorry

end ActuarialValuation
