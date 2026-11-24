-- Prove2me | Theorems.Thm_FairSelling_CanonExists_mono
-- name    : FairSelling.CanonExists.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:10.543573+00:00
-- url     : https://prove2.me/theorems/d778a980-5a4a-46a9-a865-8f1274c9c8f8
-- title:
--   Canon Exists: mono
-- statement:
--   A canonical partition of a smaller pool of goods is a canonical partition of a larger one.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsGlue.lean#L51-L60
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsGlue.lean#L51-L60

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.CanonExists.mono {w p : G → ℝ} {μ t : ℝ} {k : ℕ} {R R' : Finset G} {D D' : ℝ}
    (hR : R ⊆ R') (hD : D ≤ D') (h : CanonExists w p μ t k R D) :
    CanonExists w p μ t k R' D' := by sorry
