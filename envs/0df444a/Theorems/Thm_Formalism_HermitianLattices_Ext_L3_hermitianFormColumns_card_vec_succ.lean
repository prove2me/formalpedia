-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_card_vec_succ
-- name    : Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.card_vec_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:33.553029+00:00
-- url     : https://prove2.me/theorems/7f468434-1924-4a94-8e14-2e664e8fbdda
-- title:
--   hermitian Form Columns: card vec succ
-- statement:
--   The hermitian Form Columns construction uses the card vec succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L57-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L57-L114

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.card_vec_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (H : Matrix m m (𝓞 K)) (hH : Hᴴ = H) (n : 𝓞 F) {k j : ℕ}
    (hj : k + 1 ≤ 2 * j) (p' : (m → 𝓞 K ⧸ extP K 𝔭 ^ k) → Prop)
    (hinv : ∀ x y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ j) →
      (p' (fun i => mkk K 𝔭 k ((x + y) i)) ↔ p' (fun i => mkk K 𝔭 k (x i))))
    (RC : ∀ x : m → 𝓞 K, p' (fun i => mkk K 𝔭 k (x i)) → fm H x x - ι n ∈ extP K 𝔭 ^ k →
      ∀ s ∈ extP K 𝔭 ^ k, star s - s ∈ extP K 𝔭 ^ (k + 1) →
      ∃ y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ j) ∧ fm H x y + fm H y x - s ∈ extP K 𝔭 ^ (k + 1)) :
    Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // p' (fun i => piQ K 𝔭 k (x i)) ∧
        fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} * Ideal.absNorm 𝔭 =
      Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) *
        Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // p' x ∧
          fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} := by sorry
