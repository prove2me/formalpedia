-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_run_ok
-- name    : ClauseBound.ParityChecks.run_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:07.320535+00:00
-- url     : https://prove2.me/theorems/38a53d76-8fb8-431f-949e-66248cd1362b
-- title:
--   Parity Checks: run ok
-- statement:
--   The result of the run: r checks, each a list of clauses without repetition; they are good; and
--   the three bounds hold.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L390-L413
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L390-L413

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open Run

theorem ClauseBound.ParityChecks.run_ok (H2 : ChoiceByPotential) {ε : ℚ} (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) :
    (q.run orcA orcB).length = q.r ∧ (∀ L ∈ q.run orcA orcB, ChkOK q.m L) ∧ Good V q.nb q.r (lam q.m (q.run orcA orcB)) ∧
      ((∑ j' ∈ range q.r, #(lam q.m (q.run orcA orcB) j') : ℕ) : ℚ) < 8 * pr q.nb * q.m * q.r ∧
      (∀ j' < q.r, (2 : ℚ) ^ #(lam q.m (q.run orcA orcB) j') < 8 * q.r * (1 + pr q.nb) ^ q.m) ∧
      ∀ x : Fin q.m, (2 : ℚ) ^ #{j' ∈ range q.r | x ∈ lam q.m (q.run orcA orcB) j'} < 8 * q.m * (1 + pr q.nb) ^ q.r := by sorry
