-- Prove2me | Theorems.Thm_FairSelling_config_vbarSum_univ
-- name    : FairSelling.config_vbarSum_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:23.09655+00:00
-- url     : https://prove2.me/theorems/2fe31214-ec8c-435d-87af-c386c5a9e4fe
-- title:
--   Fair Selling: config vbar Sum univ
-- statement:
--   Total value of all goods, split along a configuration.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourResidual.lean#L31-L52
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourResidual.lean#L31-L52

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
import Definitions.Def_RequestProject_LemmaFourResidual
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.config_vbarSum_univ (w p : G → ℝ) {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ}
    {r : ℝ} (hcfg : ConfigN 3 w p r A s q) :
    vbarSum w p Finset.univ = (∑ i, vbarSum w p (A i)) + vbarSum w p s := by sorry
