-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_second_small_condition
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.second_small_condition
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:34:40.050441+00:00
-- url     : https://prove2.me/theorems/7c04a0dc-91d1-4877-82cd-8bffd8b56049
-- title:
--   Dens: second small condition
-- statement:
--   The Dens construction uses the second small condition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DyadicSizeLePowTwelveSecond.lean#L54-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DyadicSizeLePowTwelveSecond.lean#L54-L72

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.second_small_condition (u l K J q s Lq : ℝ) (hq : 0 < q) (hs : 0 < s) (hu : u ≤ 1 / (q * s))
    (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 48 * q) (hJ0 : 0 < J) (hJ : J ≤ 24 * Lq)
    (hc : 971882496 * Lq ^ 5 ≤ s) : 2 * u * l ^ 3 * K ≤ (1 / (2 * J)) ^ 2 / 2 := by sorry
