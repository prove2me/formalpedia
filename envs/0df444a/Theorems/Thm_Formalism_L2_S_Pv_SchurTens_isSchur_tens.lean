-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_isSchur_tens
-- name    : Formalism.L2.S.Pv.SchurTens.isSchur_tens
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:23.78793+00:00
-- url     : https://prove2.me/theorems/15e8002c-e90e-4229-bbe9-04cca93ad7e5
-- title:
--   Schur Tens: is Schur tens
-- statement:
--   The Schur Tens construction uses the is Schur tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensDense.lean#L224-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensDense.lean#L224-L239

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, MeasurableSpace (G v)] {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs' : Type} [NormedAddCommGroup Hs'] [InnerProductSpace ℂ Hs']
  {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs' : (∀ v, G v) → (Hs' →L[ℂ] Hs')} {tens : (∀ v, H v) → Hs'}

theorem Formalism.L2.S.Pv.SchurTens.isSchur_tens [OpensMeasurableSpace (∀ v, G v)] (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)]
    (d : ι → ℝ) (hσ : ∀ v, IsUnitRep (σ v)) (hS : ∀ v, IsSchur (μ v) (σ v) (d v)) (h : IsTensAbs σ σs' tens) :
    IsSchur (Measure.pi μ) σs' (∏ v, d v) := by sorry
