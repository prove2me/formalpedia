-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_tens_unit_all
-- name    : Formalism.L2.S.Pv.SchurTens.tens_unit_all
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:15:32.668459+00:00
-- url     : https://prove2.me/theorems/73709c22-e7ec-4358-9925-ea176b7b1e78
-- title:
--   Schur Tens: tens unit all
-- statement:
--   The Schur Tens construction uses the tens unit all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensRep.lean#L60-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensRep.lean#L60-L75

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs : (∀ v, G v) → (Hs →L[ℂ] Hs)} {tens : (∀ v, H v) → Hs}

theorem Formalism.L2.S.Pv.SchurTens.tens_unit_all (hσ : ∀ v, IsUnitRep (σ v)) (h : IsTensAbs σ σs tens) (g : ∀ v, G v) (a b : Hs) :
    ⟪σs g a, σs g b⟫_ℂ = ⟪a, b⟫_ℂ := by sorry
