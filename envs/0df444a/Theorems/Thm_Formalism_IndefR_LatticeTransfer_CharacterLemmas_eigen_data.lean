-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_CharacterLemmas_eigen_data
-- name    : Formalism.IndefR.LatticeTransfer.CharacterLemmas.eigen_data
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:16.180704+00:00
-- url     : https://prove2.me/theorems/a922f828-05c5-4bed-81f9-f31530b69245
-- title:
--   Character Lemmas: eigen data
-- statement:
--   The Character Lemmas construction uses the eigen data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/TraceOfDiag.lean#L22-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/TraceOfDiag.lean#L22-L75

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.CharacterLemmas

theorem Formalism.IndefR.LatticeTransfer.CharacterLemmas.eigen_data {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ∃ (I : Type) (_ : Fintype I) (μ : I → ℂ), Fintype.card I = finrank ℂ V ∧
      (∀ i, μ i ^ orderOf g = 1) ∧ LinearMap.trace ℂ V (ρ g) = ∑ i, μ i ∧
      LinearMap.trace ℂ V (ρ g⁻¹) = ∑ i, starRingEnd ℂ (μ i) := by sorry
