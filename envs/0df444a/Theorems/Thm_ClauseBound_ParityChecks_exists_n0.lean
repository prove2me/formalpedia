-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_exists_n0
-- name    : ClauseBound.ParityChecks.exists_n0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:53.967907+00:00
-- url     : https://prove2.me/theorems/baf670f7-53de-4298-8d32-0125ae558683
-- title:
--   Parity Checks: exists n0
-- statement:
--   For n large enough in terms of c, if 2 ≤ Δ ≤ (⌊log₂ n⌋ + 1)^c and nb < m ≤ Δ·n, the parameters
--   satisfy all that the run needs, with ε = 2^{1−10n}, and r ≤ 6n, β ≤ 5n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L530-L544
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L530-L544

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params

theorem ClauseBound.ParityChecks.exists_n0 (c : ℕ) : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ Δ m : ℕ, 2 ≤ Δ → Δ ≤ (Nat.log 2 n + 1) ^ c → nbOf n Δ < m → m ≤ Δ * n →
    Hyp (parOf n Δ m) (2 ^ n) (2 / 2 ^ (10 * n)) ∧ (parOf n Δ m).r ≤ 6 * n ∧ (parOf n Δ m).β ≤ 5 * n ∧
      beta0 m (nbOf n Δ) ≤ 4 * n ∧ nbOf n Δ * LD Δ ≤ n ∧ n < 2 * (nbOf n Δ * LD Δ) := by sorry
