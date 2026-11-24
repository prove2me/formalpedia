-- Prove2me | Theorems.Thm_Formalism_HN_PlaceLattice_sum_embedding_eq_zero
-- name    : Formalism.HN.PlaceLattice.sum_embedding_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:51.980468+00:00
-- url     : https://prove2.me/theorems/32320b38-3bd3-4f4f-9803-aa50907803d0
-- title:
--   Place Lattice: sum embedding eq zero
-- statement:
--   The Place Lattice construction uses the sum embedding eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DiscreteSpanOfLinIndep.lean#L51-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DiscreteSpanOfLinIndep.lean#L51-L65

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceLattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem Formalism.HN.PlaceLattice.sum_embedding_eq_zero {t : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ}
    (h : ∀ v : InfinitePlace K, ∑ k, (t k : ℂ) * v.embedding (integralBasis K k) = 0) : t = 0 := by sorry
