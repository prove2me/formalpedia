-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_CharacterLemmas_trace_of_diag
-- name    : Formalism.IndefR.LatticeTransfer.CharacterLemmas.trace_of_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:31.27615+00:00
-- url     : https://prove2.me/theorems/e84d4d4a-354b-425a-8031-6cec3bb45c2d
-- title:
--   Character Lemmas: trace of diag
-- statement:
--   The Character Lemmas construction uses the trace of diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/TraceOfDiag.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/TraceOfDiag.lean#L14-L20

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

theorem Formalism.IndefR.LatticeTransfer.CharacterLemmas.trace_of_diag {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I] [DecidableEq I]
    (v : Basis I ℂ V) (h : V →ₗ[ℂ] V) (c : I → ℂ) (hv : ∀ i, h (v i) = c i • v i) :
    LinearMap.trace ℂ V h = ∑ i, c i := by sorry
