-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_hsA_conj
-- name    : Formalism.L2.S.Pv.EnergyAbs.hsA_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:24:58.815775+00:00
-- url     : https://prove2.me/theorems/99edcf64-4806-4882-a3f4-3d4db3c0403b
-- title:
--   Energy Abs: hs A conj
-- statement:
--   The Energy Abs construction uses the hs A conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsBasic.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsBasic.lean#L51-L64

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem Formalism.L2.S.Pv.EnergyAbs.hsA_conj (U : V →L[ℂ] V) (U' : V' →L[ℂ] V') (hU : ∀ a b, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hU' : ∀ a b, ⟪U' a, U' b⟫_ℂ = ⟪a, b⟫_ℂ) (A : V' →L[ℂ] V) :
    hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) = hsA A := by sorry
