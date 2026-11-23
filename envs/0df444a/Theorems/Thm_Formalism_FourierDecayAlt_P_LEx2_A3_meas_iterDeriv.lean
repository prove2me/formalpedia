-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A3_meas_iterDeriv
-- name    : Formalism.FourierDecayAlt.P.LEx2.A3.meas_iterDeriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:52.482033+00:00
-- url     : https://prove2.me/theorems/ec5e23ee-d578-4cb7-b5ef-72c80ae2c152
-- title:
--   A3: meas iter Deriv
-- statement:
--   The A3 construction uses the meas iter Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasIterDeriv.lean#L21-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasIterDeriv.lean#L21-L46

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A3
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section

theorem Formalism.FourierDecayAlt.P.LEx2.A3.meas_iterDeriv {Ω : Type} [MeasurableSpace Ω] (F : ℝ → Ω → ℂ)
    (hsm : ∀ ω, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => F s ω)) (hm : ∀ s, Measurable (F s)) :
    ∀ (p : ℕ) (s : ℝ), Measurable (fun ω => iteratedDeriv p (fun s => F s ω) s) := by sorry
