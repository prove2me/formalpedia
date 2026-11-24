-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_norm_sq_yv
-- name    : Formalism.L2.Geo.Rec.DualLatticeEmbeddings.norm_sq_yv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:58.477932+00:00
-- url     : https://prove2.me/theorems/435eb7b8-de2a-474d-aa3b-324bbde8d066
-- title:
--   Dual Lattice Embeddings: norm sq yv
-- statement:
--   The Dual Lattice Embeddings construction uses the norm sq yv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L276-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L276-L301

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

theorem Formalism.L2.Geo.Rec.DualLatticeEmbeddings.norm_sq_yv (cj : K → K) (hσ : ∀ (v : InfinitePlace K) z, v.embedding (cj z) = star (v.embedding z))
    (A : Matrix (Fin n) (Fin n) K) (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hfr : ∀ v, Xf v * (Xf v)ᴴ = A.map v.embedding) (ξ : Fin n → K) :
    ‖yv Xf ξ‖ ^ 2 = 4 * ∑ v : InfinitePlace K, (v.embedding (∑ i, ∑ k, ξ i * A i k * cj (ξ k))).re := by sorry
