-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sum_excI_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.sum_excI_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:17:37.538611+00:00
-- url     : https://prove2.me/theorems/6e088c2b-a2fd-44b3-8268-2f1b23efdf7a
-- title:
--   Primes In Progressions: sum exc I le
-- statement:
--   The Primes In Progressions construction uses the sum exc I le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmB.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmB.lean#L30-L37

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTBAsmB
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.sum_excI_le {M : ℕ} [NeZero M] (e : Option (DirichletCharacter ℂ M × ℝ)) :
    ∑ χ : DirichletCharacter ℂ M, excI e χ ≤ 1 := by sorry
