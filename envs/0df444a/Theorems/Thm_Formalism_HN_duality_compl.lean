-- Prove2me | Theorems.Thm_Formalism_HN_duality_compl
-- name    : Formalism.HN.duality_compl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:00.766532+00:00
-- url     : https://prove2.me/theorems/c2c65edb-c8a8-4e36-b48f-b3291cc81a2c
-- title:
--   HN: duality compl
-- statement:
--   The HN construction uses the duality compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L248-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L248-L270

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [FiniteDimensional ℝ E]

theorem Formalism.HN.duality_compl (L S : Submodule ℤ E) [hL : DiscreteTopology L] (hS : S ≤ L) :
    ∃ N : Submodule ℤ E, N ≤ dualZ L ∧ Formalism.F.rk N + Formalism.F.rk S = Formalism.F.rk L ∧
      Formalism.F.deg S - Formalism.F.deg L ≤ Formalism.F.deg N := by sorry
