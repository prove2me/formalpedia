-- Prove2me | Theorems.Thm_Formalism_HN_PlaceLattice_discrete_span_of_linIndep
-- name    : Formalism.HN.PlaceLattice.discrete_span_of_linIndep
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:44.24081+00:00
-- url     : https://prove2.me/theorems/f527122a-fb69-4901-9109-09cd26bc4a58
-- title:
--   Place Lattice: discrete span of lin Indep
-- statement:
--   The Place Lattice construction uses the discrete span of lin Indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DiscreteSpanOfLinIndep.lean#L129-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DiscreteSpanOfLinIndep.lean#L129-L165

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

theorem Formalism.HN.PlaceLattice.discrete_span_of_linIndep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι' : Type*} {f : ι' → E} (hf : LinearIndependent ℝ f) :
    DiscreteTopology (Submodule.span ℤ (Set.range f)) := by sorry
