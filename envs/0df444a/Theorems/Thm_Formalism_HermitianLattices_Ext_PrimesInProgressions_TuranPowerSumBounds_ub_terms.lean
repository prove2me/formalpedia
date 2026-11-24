-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_ub_terms
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.ub_terms
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:49.744455+00:00
-- url     : https://prove2.me/theorems/0bd7dda2-8c85-4c3f-88a0-4d10299b01f2
-- title:
--   Turan Power Sum Bounds: ub terms
-- statement:
--   The Turan Power Sum Bounds construction uses the ub terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/UbTerms.lean#L84-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/UbTerms.lean#L84-L184

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_UbTerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
set_option maxHeartbeats 800000

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.ub_terms (a : ℕ) (CP CF cZ cS c₂ κ L ℓ lam η Mr K : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hCP : 0 < CP) (hCF : 0 < CF) (hcZ : 0 < cZ) (hcS : 0 < cS) (hc₂ : 0 < c₂)
    (hL : 1 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 2 * L) (hlam : 0 < lam) (hη : 0 < η) (hMr : 0 < Mr) (hK : 0 < K)
    (hlη1 : lam / η ≤ 2 * (lam * L) / cZ) (hM : ℓ ^ 2 / Mr ≤ 32 * lam / cS) (hηc : η ≤ c0 a)
    (hηL : η * L < c₂ * K) (h25c : 25 * CF * c₂ ≤ κ) (hκth : κ ≤ th a)
    (hc₂P : 2 * Real.exp 1 * CP * c₂ * rr a ≤ th a) (hjr : th a * K < j) :
    η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ)
        + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * j * lam / η ^ (j + 1) + CF * L * 25 ^ j) ≤
      (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by sorry
