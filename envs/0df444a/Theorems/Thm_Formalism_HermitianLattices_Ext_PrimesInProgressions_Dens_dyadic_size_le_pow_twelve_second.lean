-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_dyadic_size_le_pow_twelve_second
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.dyadic_size_le_pow_twelve_second
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:45:00.154128+00:00
-- url     : https://prove2.me/theorems/e89c037f-f1eb-4cff-a52c-245e50367459
-- title:
--   Dens: dyadic size le pow twelve second
-- statement:
--   The Dens construction uses the dyadic size le pow twelve second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DyadicSizeLePowTwelveSecond.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DyadicSizeLePowTwelveSecond.lean#L46-L52

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DyadicSizeLePowTwelveSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.dyadic_size_le_pow_twelve_second (q : ℕ) (hq : 256 ≤ q) : q ^ 3 * 2 ^ (8 * (Nat.log 2 q + 1)) ≤ q ^ 12 := by sorry
