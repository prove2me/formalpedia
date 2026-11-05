-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_prod_choose_le
-- name    : ClauseBound.ParityChecks.prod_choose_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:50.634135+00:00
-- url     : https://prove2.me/theorems/00cc8f72-52da-4314-81fe-cec28d796ad7
-- title:
--   Parity Checks: prod choose le
-- statement:
--   A product of binomial coefficients is at most the binomial coefficient of the sums.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Binom.lean#L45-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Binom.lean#L45-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Binom
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Binom

theorem ClauseBound.ParityChecks.prod_choose_le {ι : Type} (s : Finset ι) (t μ : ι → ℕ) : ∏ i ∈ s, (t i).choose (μ i) ≤ (∑ i ∈ s, t i).choose (∑ i ∈ s, μ i) := by sorry
