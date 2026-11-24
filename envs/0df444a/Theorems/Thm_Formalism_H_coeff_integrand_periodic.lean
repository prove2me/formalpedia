-- Prove2me | Theorems.Thm_Formalism_H_coeff_integrand_periodic
-- name    : Formalism.H.coeff_integrand_periodic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:12.845593+00:00
-- url     : https://prove2.me/theorems/f825dd7c-c778-4c03-bce7-425d87a41691
-- title:
--   H: coeff integrand periodic
-- statement:
--   The H construction uses the coeff integrand periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/LatticeFourierSeries.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/LatticeFourierSeries.lean#L13-L27

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_TorusProjIsOpenQuotientMap
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem Formalism.H.coeff_integrand_periodic (Λ : Submodule ℤ V) (G : V → ℂ)
    (hper : ∀ (l : Λ) (x : V), G ((l : V) + x) = G x) (μ : V) (hμ : μ ∈ dual Λ) (l : Λ) (y : V) :
    G ((l : V) + y) * Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, (l : V) + y⟫ : ℝ))) =
      G y * Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) := by sorry
