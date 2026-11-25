-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_eOf_exc
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.eOf_exc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:36:30.20281+00:00
-- url     : https://prove2.me/theorems/d267ff67-1d2f-5838-997e-7d65bc0ad826
-- title:
--   Primes In Progressions: e Of exc
-- statement:
--   The Primes In Progressions construction uses the e Of exc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean#L47-L57

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.eOf_exc (M : ℕ) [NeZero M] (p : DirichletCharacter ℂ M × ℝ) (h : eOf M = some p) :
    IsExcPair p.1 p.2 := by sorry
