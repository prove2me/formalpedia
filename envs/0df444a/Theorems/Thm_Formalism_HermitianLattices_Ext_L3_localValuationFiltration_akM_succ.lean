-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_akM_succ
-- name    : Formalism.HermitianLattices.Ext.L3.localValuationFiltration.akM_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:54.133629+00:00
-- url     : https://prove2.me/theorems/868af048-f94f-4073-9497-fa14440c6501
-- title:
--   local Valuation Filtration: ak M succ
-- statement:
--   The local Valuation Filtration construction uses the ak M succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocalData.lean#L119-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocalData.lean#L119-L165

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localValuationFiltration
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)] {m : Type} [Fintype m] [DecidableEq m]

theorem Formalism.HermitianLattices.Ext.L3.localValuationFiltration.akM_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D : 𝓞 F} (hD : H.det = ι D) {c k : ℕ}
    (hDc : D ∉ 𝔭 ^ (c + 1)) (hk : 2 * c + 1 ≤ k) :
    Nat.card {X : Matrix m m (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) //
        Xᴴ * H.map (mkk K 𝔭 (k + 1)) * X = H.map (mkk K 𝔭 (k + 1))} =
      Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m) *
        Nat.card {X : Matrix m m (𝓞 K ⧸ extP K 𝔭 ^ k) //
          Xᴴ * H.map (mkk K 𝔭 k) * X = H.map (mkk K 𝔭 k)} := by sorry
