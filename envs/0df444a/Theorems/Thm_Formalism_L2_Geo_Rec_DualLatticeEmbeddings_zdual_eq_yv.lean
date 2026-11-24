-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_zdual_eq_yv
-- name    : Formalism.L2.Geo.Rec.DualLatticeEmbeddings.zdual_eq_yv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:24.422796+00:00
-- url     : https://prove2.me/theorems/8a0e27d0-dd8d-498d-8aa3-c7763dd3e5bd
-- title:
--   Dual Lattice Embeddings: zdual eq yv
-- statement:
--   The Dual Lattice Embeddings construction uses the zdual eq yv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L207-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L207-L270

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

theorem Formalism.L2.Geo.Rec.DualLatticeEmbeddings.zdual_eq_yv (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hXf : ∀ v, IsUnit (Xf v).det)
    (X : Submodule (𝓞 K) (Fin n → K)) (hX : Submodule.span K (X : Set (Fin n → K)) = ⊤)
    (y : Amb K n) (hy : y ∈ Formalism.HadamardInequality.zdual (Mz Xf X)) :
    ∃ ξ : Fin n → K, y = yv Xf ξ ∧
      ∀ x ∈ X, Algebra.trace ℚ K (∑ i, ξ i * x i) ∈ Set.range (Int.cast : ℤ → ℚ) := by sorry
