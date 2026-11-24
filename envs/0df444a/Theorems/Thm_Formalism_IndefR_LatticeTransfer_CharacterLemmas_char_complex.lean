-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_CharacterLemmas_char_complex
-- name    : Formalism.IndefR.LatticeTransfer.CharacterLemmas.char_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:21.680243+00:00
-- url     : https://prove2.me/theorems/3aee7a64-8ebf-437b-a50e-e7ff48ae05c9
-- title:
--   Character Lemmas: char complex
-- statement:
--   The Character Lemmas construction uses the char complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/TraceOfDiag.lean#L77-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/TraceOfDiag.lean#L77-L97

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

theorem Formalism.IndefR.LatticeTransfer.CharacterLemmas.char_complex {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    IsIntegral ℤ (LinearMap.trace ℂ V (ρ g)) ∧
      LinearMap.trace ℂ V (ρ g⁻¹) = star (LinearMap.trace ℂ V (ρ g)) ∧
      ‖LinearMap.trace ℂ V (ρ g)‖ ≤ (finrank ℂ V : ℝ) := by sorry
