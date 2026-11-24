-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_matrix_of_isom
-- name    : Formalism.HermitianLattices.Ext.L3.HU.exists_matrix_of_isom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:50.354815+00:00
-- url     : https://prove2.me/theorems/c31f1b7a-e8b3-44ba-a24a-d4c73217cb28
-- title:
--   HU: exists matrix of isom
-- statement:
--   The HU construction uses the exists matrix of isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMatrixOfIsom.lean#L156-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMatrixOfIsom.lean#L156-L194

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsUnitaryNear
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem Formalism.HermitianLattices.Ext.L3.HU.exists_matrix_of_isom (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b))) (N : ℕ) :
    ∃ Y : Matrix κ κ (𝓞 K), (∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ N) ∧
      ∀ i, g (b i) - ∑ l, Y l i • b l ∈ (extP K 𝔭 ^ N • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by sorry
