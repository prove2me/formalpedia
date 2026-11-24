-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_inner_mkE
-- name    : Formalism.L2.Geo.Rec.DualLatticeEmbeddings.inner_mkE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:41.455056+00:00
-- url     : https://prove2.me/theorems/c630e496-76f7-47d1-8801-c361c930b9b5
-- title:
--   Dual Lattice Embeddings: inner mk E
-- statement:
--   The Dual Lattice Embeddings construction uses the inner mk E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L24-L29

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem Formalism.L2.Geo.Rec.DualLatticeEmbeddings.inner_mkE (a c : InfinitePlace K → Fin n → ℂ) :
    inner ℝ (mkE a) (mkE c) = ∑ v, ∑ i, (star (a v i) * c v i).re := by sorry
