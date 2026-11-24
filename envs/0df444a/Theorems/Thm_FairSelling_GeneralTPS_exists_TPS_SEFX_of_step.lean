-- Prove2me | Theorems.Thm_FairSelling_GeneralTPS_exists_TPS_SEFX_of_step
-- name    : FairSelling.GeneralTPS.exists_TPS_SEFX_of_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:42:13.944433+00:00
-- url     : https://prove2.me/theorems/56cc3bb1-cd5e-433e-b51b-3cfa2a79a5b8
-- title:
--   General TPS: exists TPS SEFX of step
-- statement:
--   **Theorem 2 (SEFX half) reduces to the improvement step.**  If for every `ε > 0` the
--   improvement step of Algorithm 6 can always be performed, then every allocation instance admits a
--   valid outcome that gives every agent at least `n/(2n−1)` of its truncated proportional share and
--   is SEFX.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L395-L410
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L395-L410

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.GeneralTPS.exists_TPS_SEFX_of_step (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g)
    (hstep : ∀ eps : ℝ, 0 < eps → ImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by sorry
