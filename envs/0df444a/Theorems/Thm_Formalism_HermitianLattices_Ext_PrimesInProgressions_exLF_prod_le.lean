-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_prod_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_prod_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:59.571338+00:00
-- url     : https://prove2.me/theorems/c8302cbb-1f9d-5046-a695-1dcc71f10513
-- title:
--   Primes In Progressions: ex LF prod le
-- statement:
--   The Primes In Progressions construction uses the ex LF prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L106-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L106-L127

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
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
variable {M : ℕ} [NeZero M]

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_prod_le (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ M := by sorry
