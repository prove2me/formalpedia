-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_core2
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.core2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:48.627388+00:00
-- url     : https://prove2.me/theorems/cccabb29-d486-4de8-8714-159f51bd55d9
-- title:
--   Turan Power Sum Bounds: core2
-- statement:
--   The Turan Power Sum Bounds construction uses the core2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/NormUSum.lean#L20-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/NormUSum.lean#L20-L160

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_UbTerms
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_NormUSum
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.core2 (CT : ℝ) (a : ℕ) (hCT : 0 < CT) (ha : 1 ≤ a)
    (hT : ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n → (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
      ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + a * n ∧ ((n : ℝ) / (CT * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i, z i ^ k‖)
    (CF CP cZ cS c₁ c₂ : ℝ) (hCF : 0 < CF) (hCP : 0 < CP) (hcZ : 0 < cZ) (hcS : 0 < cS) (hc₁ : 0 < c₁)
    (hc₁Z : c₁ ≤ cZ / 4) (hc₂ : 0 < c₂)
    (hc₂κ : c₂ ≤ kap a (Real.log (max CT 1)) / (25 * CF))
    (hc₂P : c₂ ≤ th a / (2 * Real.exp 1 * CP * rr a))
    (L ℓ lam η Mr K : ℝ) (hL : 1 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 2 * L) (hlam : 0 < lam)
    (hηZ : cZ / (2 * L) ≤ η) (hηc : η ≤ c0 a) (hηL : η * L < c₂ * K) (hMr : 0 < Mr)
    (hM : ℓ ^ 2 / Mr ≤ 32 * lam / cS) (hX : lam * L ^ 3 = c₁ * Real.exp (-K))
    (hK : K0 a (Real.log (max CT 1)) CP cZ cS c₁ < K)
    (N : ℕ) (w : Fin N → ℂ) (hw : ∀ i, η ≤ (w i).re) (hi0 : ∃ i, w i = ((η + η : ℝ) : ℂ))
    (hS : (∑ i, 1 / w i).re ≤ 2 * lam / η ^ 2 + CF * L * 25)
    (hpow : ∀ j : ℕ, 1 ≤ j → ‖∑ i, 1 / (w i) ^ j‖ ≤
        CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ)
        + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * j * lam / η ^ (j + 1) + CF * L * 25 ^ j) :
    False := by sorry
