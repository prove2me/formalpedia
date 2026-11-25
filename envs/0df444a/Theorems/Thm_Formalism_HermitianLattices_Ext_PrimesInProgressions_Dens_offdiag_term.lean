-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_offdiag_term
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.offdiag_term
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:35:16.44781+00:00
-- url     : https://prove2.me/theorems/2274065b-674e-4f4e-b85c-1b70b5e371f3
-- title:
--   Dens: offdiag term
-- statement:
--   The Dens construction uses the offdiag term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensBlock.lean#L24-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensBlock.lean#L24-L106

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensDiv
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensBlock
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.offdiag_term {M : ℕ} [NeZero M] (σ T : ℝ) (U : ℕ) (hU : 1 ≤ U) (hT : 2 ≤ T) (hσ : 1 / 2 ≤ σ)
    (p p' : DirichletCharacter ℂ M × ℂ)
    (hp : σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T) (hp' : σ ≤ p'.2.re ∧ p'.2.re ≤ 1 ∧ |p'.2.im| ≤ T)
    (hsp : p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) :
    ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-((p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ))))‖ ≤
      (if p' = p then (U : ℝ) else 0) +
        (if p'.1 = p.1 then 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) else 0) +
        4 * ((M : ℝ) + 1) * (2 + 2 * T) := by sorry
