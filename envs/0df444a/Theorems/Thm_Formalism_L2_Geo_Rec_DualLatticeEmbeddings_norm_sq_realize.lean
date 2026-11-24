-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_norm_sq_realize
-- name    : Formalism.L2.Geo.Rec.DualLatticeEmbeddings.norm_sq_realize
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:41.352272+00:00
-- url     : https://prove2.me/theorems/942bc0bd-b661-4fde-b40d-3287aa90135b
-- title:
--   Dual Lattice Embeddings: norm sq realize
-- statement:
--   The Dual Lattice Embeddings construction uses the norm sq realize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L272-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L272-L274

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
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ} [StarRing K] [IsTotallyComplex K]

theorem Formalism.L2.Geo.Rec.DualLatticeEmbeddings.norm_sq_realize (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x‖ ^ 2 = ∑ v, ∑ i, ‖fc Xf v x i‖ ^ 2 := by sorry
