-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_Z
-- name    : Formalism.HermitianLattices.Ext.L3.HU.exists_Z
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:59.467196+00:00
-- url     : https://prove2.me/theorems/b2dc4d32-8abc-44df-af54-6565ebe20943
-- title:
--   HU: exists Z
-- statement:
--   The HU construction uses the exists Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMatrixOfIsom.lean#L64-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMatrixOfIsom.lean#L64-L76

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

theorem Formalism.HermitianLattices.Ext.L3.HU.exists_Z {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀)
    {H Y : Matrix κ κ (𝓞 K)} {k : ℕ} (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) :
    ∃ Z : Matrix κ κ K, Ent (SP K 𝔭) Z ∧
      (Y.map jK)ᴴ * H.map jK * Y.map jK = H.map jK + jK (ι π₀) ^ k • Z := by sorry
