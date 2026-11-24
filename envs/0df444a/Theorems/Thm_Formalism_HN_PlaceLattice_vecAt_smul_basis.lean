-- Prove2me | Theorems.Thm_Formalism_HN_PlaceLattice_vecAt_smul_basis
-- name    : Formalism.HN.PlaceLattice.vecAt_smul_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:57.716051+00:00
-- url     : https://prove2.me/theorems/88bc6a52-4900-4064-9a5b-332ac2a54b52
-- title:
--   Place Lattice: vec At smul basis
-- statement:
--   The Place Lattice construction uses the vec At smul basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DiscreteSpanOfLinIndep.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DiscreteSpanOfLinIndep.lean#L67-L74

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

theorem Formalism.HN.PlaceLattice.vecAt_smul_basis (b : Basis ι K V) (v : InfinitePlace K) (a : K) (i : ι) :
    Formalism.HermitianLatticesTheory.vecAt b v (a • b i) = Pi.single i (v.embedding a) := by sorry
