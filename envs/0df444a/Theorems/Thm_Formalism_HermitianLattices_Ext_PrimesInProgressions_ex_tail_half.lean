-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_tail_half
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_tail_half
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:34.937008+00:00
-- url     : https://prove2.me/theorems/27016cc4-32bd-558c-b60b-3d5512835a6b
-- title:
--   Primes In Progressions: ex tail half
-- statement:
--   The Primes In Progressions construction uses the ex tail half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplEdge.lean#L75-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplEdge.lean#L75-L91

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplEdge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_tail_half (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T)
    (hf : ∀ t : ℝ, T < t → ‖f t‖ ≤ K / t ^ 2) :
    ‖∫ t in Set.Ioi T, f t‖ ≤ K / T := by sorry
