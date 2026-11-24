-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_sum_ulift_finset_fin_two_expand
-- name    : Formalism.L2.Geo.Rec.DualLatticeEmbeddings.sum_ulift_finset_fin_two_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:04.862504+00:00
-- url     : https://prove2.me/theorems/e39c0cb4-6c29-4ab4-bfae-34610dc79443
-- title:
--   Dual Lattice Embeddings: sum ulift finset fin two expand
-- statement:
--   The Dual Lattice Embeddings construction uses the sum ulift finset fin two expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L22-L22

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

theorem Formalism.L2.Geo.Rec.DualLatticeEmbeddings.sum_ulift_finset_fin_two_expand (g : Fin 2 → ℝ) : ∑ k, g k = g 0 + g 1 := by sorry
