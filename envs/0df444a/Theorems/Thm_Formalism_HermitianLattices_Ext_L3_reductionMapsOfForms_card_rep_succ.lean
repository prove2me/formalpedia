-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_card_rep_succ
-- name    : Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.card_rep_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:59.017829+00:00
-- url     : https://prove2.me/theorems/cdb59e50-f324-4f5c-8f66-2d09e2a0cfac
-- title:
--   reduction Maps Of Forms: card rep succ
-- statement:
--   The reduction Maps Of Forms construction uses the card rep succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEighth.lean#L66-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEighth.lean#L66-L146

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m r : Type} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.card_rep_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (H : Matrix m m (𝓞 K)) (hH : Hᴴ = H) (T : Matrix r r (𝓞 K)) (hT : Tᴴ = T) {k j : ℕ}
    (hj : k + 1 ≤ 2 * j) (p' : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ k) → Prop)
    (hinv : ∀ X Y : Matrix m r (𝓞 K), (∀ a b, Y a b ∈ extP K 𝔭 ^ j) →
      (p' ((X + Y).map (mkk K 𝔭 k)) ↔ p' (X.map (mkk K 𝔭 k))))
    (RC : ∀ X : Matrix m r (𝓞 K), p' (X.map (mkk K 𝔭 k)) →
      (∀ a b, (Xᴴ * H * X - T) a b ∈ extP K 𝔭 ^ k) → ∀ S : Matrix r r (𝓞 K),
      (∀ a b, S a b ∈ extP K 𝔭 ^ k) → (∀ a b, (Sᴴ - S) a b ∈ extP K 𝔭 ^ (k + 1)) →
      ∃ Y : Matrix m r (𝓞 K), (∀ a b, Y a b ∈ extP K 𝔭 ^ j) ∧
        ∀ a b, (Xᴴ * H * Y + Yᴴ * H * X - S) a b ∈ extP K 𝔭 ^ (k + 1)) :
    Nat.card {X : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) // p' (X.map (piQ K 𝔭 k)) ∧
        Xᴴ * H.map (mkk K 𝔭 (k + 1)) * X = T.map (mkk K 𝔭 (k + 1))} *
        Ideal.absNorm 𝔭 ^ (Fintype.card r * Fintype.card r) =
      Ideal.absNorm 𝔭 ^ (2 * (Fintype.card m * Fintype.card r)) *
        Nat.card {X : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ k) // p' X ∧
          Xᴴ * H.map (mkk K 𝔭 k) * X = T.map (mkk K 𝔭 k)} := by sorry
