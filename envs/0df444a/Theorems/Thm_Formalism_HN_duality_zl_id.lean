-- Prove2me | Theorems.Thm_Formalism_HN_duality_zl_id
-- name    : Formalism.HN.duality_zl_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:09.052735+00:00
-- url     : https://prove2.me/theorems/4c6ff7fb-dc54-4efa-9c7d-028b763efba6
-- title:
--   HN: duality zl id
-- statement:
--   The HN construction uses the duality zl id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L272-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L272-L275

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

theorem Formalism.HN.duality_zl_id (N : Submodule ℤ E) : zl (AddMonoidHom.id E) N = N := by sorry
