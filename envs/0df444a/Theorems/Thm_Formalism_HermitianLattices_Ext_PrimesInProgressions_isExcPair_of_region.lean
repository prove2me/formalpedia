-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_isExcPair_of_region
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.isExcPair_of_region
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:29:32.980805+00:00
-- url     : https://prove2.me/theorems/415bf5ce-d81e-4b23-b3e1-8d5879a838da
-- title:
--   Primes In Progressions: is Exc Pair of region
-- statement:
--   The Primes In Progressions construction uses the is Exc Pair of region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean#L83-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean#L83-L100

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.isExcPair_of_region (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (β : ℝ)
    (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1) (hz : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hr : InRegion cZ M (β : ℂ)) : IsExcPair χ β := by sorry
