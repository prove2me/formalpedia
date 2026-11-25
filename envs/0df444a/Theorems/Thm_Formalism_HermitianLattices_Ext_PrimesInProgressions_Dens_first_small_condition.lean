-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_first_small_condition
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.first_small_condition
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:45:08.593231+00:00
-- url     : https://prove2.me/theorems/b0c4bb87-d06f-40ef-9363-69f8665bcc55
-- title:
--   Dens: first small condition
-- statement:
--   The Dens construction uses the first small condition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/OneLeLogOfThreeLe.lean#L67-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/OneLeLogOfThreeLe.lean#L67-L92

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_OneLeLogOfThreeLe
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.first_small_condition (u l K J q s Lq c : ℝ) (hq : 0 < q) (hs : 0 < s) (hc0 : 0 < c)
    (hu : u ≤ 1 / (q * s)) (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 16 * q)
    (hJ0 : 0 < J) (hJ : J ≤ 25 * Lq) (hc : 87880000 / c ^ 2 * Lq ^ 7 ≤ s) :
    2 * u * l ^ 3 * K ≤ (c / (J * Lq)) ^ 2 / 2 := by sorry
