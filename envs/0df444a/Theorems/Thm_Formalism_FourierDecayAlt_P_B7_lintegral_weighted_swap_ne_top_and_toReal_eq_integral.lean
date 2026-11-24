-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_lintegral_weighted_swap_ne_top_and_toReal_eq_integral
-- name    : Formalism.FourierDecayAlt.P.B7.lintegral_weighted_swap_ne_top_and_toReal_eq_integral
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:07:14.815231+00:00
-- url     : https://prove2.me/theorems/360a8295-df0e-400e-81eb-91b371ab7d49
-- title:
--   B7: lintegral weighted swap ne top and to Real eq integral
-- statement:
--   The B7 construction uses the lintegral weighted swap ne top and to Real eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1574-L1624
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1574-L1624

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.B7.lintegral_weighted_swap_ne_top_and_toReal_eq_integral {Tt Q : Type*} [MeasurableSpace Tt] [MeasurableSpace Q] {ν : Measure Tt} {μ : Measure Q}
    [SFinite ν] [SFinite μ]
    (Wt : Tt → ℝ) (hWm : Measurable Wt) (hW0 : ∀ τ, 0 ≤ Wt τ) (w : Q → ℝ) (hwm : Measurable w)
    (hw0 : ∀ q, 0 ≤ w q)
    (n : Tt → Q → ℝ) (hnm : Measurable (fun a : Tt × Q => n a.1 a.2)) (hn0 : ∀ τ q, 0 ≤ n τ q)
    (H : Q → ℂ) (hH : Integrable (fun q => (w q : ℂ) * H q) μ)
    (hgood : ∀ᵐ q ∂μ, w q = 0 ∨
      (Integrable (fun τ => Wt τ * n τ q) ν ∧ ((∫ τ, Wt τ * n τ q ∂ν : ℝ) : ℂ) = H q)) :
    (∫⁻ τ, ENNReal.ofReal (Wt τ) * ∫⁻ q, ENNReal.ofReal (w q * n τ q) ∂μ ∂ν) ≠ ∞ ∧
    (((∫⁻ τ, ENNReal.ofReal (Wt τ) * ∫⁻ q, ENNReal.ofReal (w q * n τ q) ∂μ ∂ν).toReal : ℝ) : ℂ) =
      ∫ q, (w q : ℂ) * H q ∂μ := by sorry
