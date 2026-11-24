-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_left_num
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_left_num
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:22.328833+00:00
-- url     : https://prove2.me/theorems/cc936c1a-bdda-4c96-8417-f6bc9e93f563
-- title:
--   Primes In Progressions: exm left num
-- statement:
--   The Primes In Progressions construction uses the exm left num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L152-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L152-L236

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_left_num (κ G N M T T' σ₁ y : ℝ) (hκ : 0 < κ) (hκ' : κ ≤ 1 / 20) (hG : 0 ≤ G) (hN0 : 0 ≤ N)
    (hN : N ≤ G * (T * Real.log (M * T) ^ 2)) (hM : 3 ≤ M) (hT : 2 ≤ T) (hT0' : T ≤ T') (hT' : T' ≤ T + 1)
    (hσ : 1 - κ ≤ σ₁) (hσ' : σ₁ ≤ 1 - 3 * κ / 4) (hy : 2 ≤ y) :
    1 / (2 * Real.pi * y) * (2 * T' * (N + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁))) ≤
      3 * (G + 4 / (3 * κ)) * (2 / κ) * ((M * T) ^ 4 * y ^ (-(κ / 2))) := by sorry
