-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_inner_mkE_fc
-- name    : Formalism.L2.Geo.Rec.DualLatticeEmbeddings.inner_mkE_fc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:34.084713+00:00
-- url     : https://prove2.me/theorems/c1527407-f1db-44c4-ad16-e0054f62144e
-- title:
--   Dual Lattice Embeddings: inner mk E fc
-- statement:
--   The Dual Lattice Embeddings construction uses the inner mk E fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L52-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L52-L69

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
variable [StarRing K]

theorem Formalism.L2.Geo.Rec.DualLatticeEmbeddings.inner_mkE_fc (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hXf : ∀ v, IsUnit (Xf v).det)
    (x ξ : Fin n → K) (v : InfinitePlace K) :
    ∑ i, (star (fc Xf v x i) * ((2 : ℂ) • ((Xf v)ᴴ *ᵥ (fun i => star (v.embedding (ξ i))))) i).re =
      2 * (v.embedding (∑ i, ξ i * x i)).re := by sorry
