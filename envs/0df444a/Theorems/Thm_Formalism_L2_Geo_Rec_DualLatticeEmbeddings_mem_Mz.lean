-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_mem_Mz
-- name    : Formalism.L2.Geo.Rec.DualLatticeEmbeddings.mem_Mz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:00.355492+00:00
-- url     : https://prove2.me/theorems/41949e6c-dc9a-4464-9cc5-0e71cf29854c
-- title:
--   Dual Lattice Embeddings: mem Mz
-- statement:
--   The Dual Lattice Embeddings construction uses the mem Mz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean#L163-L167

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
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
variable [StarRing K]

theorem Formalism.L2.Geo.Rec.DualLatticeEmbeddings.mem_Mz (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (X : Submodule (𝓞 K) (Fin n → K))
    (z : Amb K n) : z ∈ Mz Xf X ↔ ∃ x ∈ X, Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x = z := by sorry
