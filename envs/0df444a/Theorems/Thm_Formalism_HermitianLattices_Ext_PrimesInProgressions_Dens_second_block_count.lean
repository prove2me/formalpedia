-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_second_block_count
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.second_block_count
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:50.879707+00:00
-- url     : https://prove2.me/theorems/5f235eed-da7a-407a-8c23-cee430c4c9f8
-- title:
--   Dens: second block count
-- statement:
--   The Dens construction uses the second block count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/SecondBlockCount.lean#L13-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/SecondBlockCount.lean#L13-L85

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensBlock
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ZeroDetectionSecond
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DyadicSizeLePowTwelveSecond
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_SecondBlockCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.second_block_count (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)) (U : ℕ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hq : 256 ≤ qd M T)
    (hc : 971882496 * Real.log (qd M T) ^ 5 ≤ Real.sqrt (qd M T))
    (hU1 : qd M T ^ 3 ≤ U) (hU2 : 2 * U ≤ qd M T ^ 12)
    (hS : ∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T)
    (hsp : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|)
    (hbig : ∀ p ∈ S, 1 / (2 * (pJd M T : ℝ)) ≤
      ‖blkD (pYd M T) (pNd M T) U (fun n => p.1 (n : ZMod M)) p.2‖) :
    (S.card : ℝ) ≤ 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) * (4 * (48 * Real.log ((M : ℝ) * T)) ^ 2) := by sorry
