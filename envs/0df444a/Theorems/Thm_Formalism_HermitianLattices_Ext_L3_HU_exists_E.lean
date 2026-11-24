-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_E
-- name    : Formalism.HermitianLattices.Ext.L3.HU.exists_E
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:11.211569+00:00
-- url     : https://prove2.me/theorems/8d195421-9da2-4b54-aa64-9bc4b3cc3b4a
-- title:
--   HU: exists E
-- statement:
--   The HU construction uses the exists E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMatrixOfIsom.lean#L34-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMatrixOfIsom.lean#L34-L53

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

theorem Formalism.HermitianLattices.Ext.L3.HU.exists_E (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {e : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) {π₀ : 𝓞 F} (hπ : π₀ ∈ 𝔭) :
    ∃ E : Matrix κ κ K, Ent (SP K 𝔭) E ∧ gramK h b * E = jK (ι π₀) ^ e • (1 : Matrix κ κ K) := by sorry
