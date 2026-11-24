-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_inner_yv
-- name    : Formalism.L2.Geo.Rec.DualLatticeEmbeddings.inner_yv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:08.352229+00:00
-- url     : https://prove2.me/theorems/28325b25-4885-4bf2-ab52-63ada1170dee
-- title:
--   Dual Lattice Embeddings: inner yv
-- statement:
--   The Dual Lattice Embeddings construction uses the inner yv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L110-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L110-L117

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
variable [IsTotallyComplex K]

theorem Formalism.L2.Geo.Rec.DualLatticeEmbeddings.inner_yv (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hXf : ∀ v, IsUnit (Xf v).det)
    (x ξ : Fin n → K) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x) (yv Xf ξ) =
      ((Algebra.trace ℚ K (∑ i, ξ i * x i) : ℚ) : ℝ) := by sorry
