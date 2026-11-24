-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_notMem_pow_vF
-- name    : Formalism.HermitianLattices.Ext.L3.localValuationFiltration.notMem_pow_vF
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:52.45618+00:00
-- url     : https://prove2.me/theorems/0c15b29d-93d9-486d-985a-2b9466f626a9
-- title:
--   local Valuation Filtration: not Mem pow v F
-- statement:
--   The local Valuation Filtration construction uses the not Mem pow v F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocalData.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocalData.lean#L47-L52

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

theorem Formalism.HermitianLattices.Ext.L3.localValuationFiltration.notMem_pow_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    n ∉ 𝔭 ^ (vF 𝔭 n + 1) := by sorry
