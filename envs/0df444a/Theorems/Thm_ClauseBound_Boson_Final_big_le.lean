-- Prove2me | Theorems.Thm_ClauseBound_Boson_Final_big_le
-- name    : ClauseBound.Boson.Final.big_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:53.935216+00:00
-- url     : https://prove2.me/theorems/63b6b88a-a477-4fe2-bee0-ee95dbb4d8f4
-- title:
--   Final: big le
-- statement:
--   If h ≤ c₀·λ² and the partitions of the integers up to 4h are at most 2^(c₂·λ), then big h ≤
--   (2λ)^c for c = c₁ + 4 + 40(c₀ + 1)² + c₂.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Final.lean#L37-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Final.lean#L37-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Boson_Final
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Final

theorem ClauseBound.Boson.Final.big_le {c₀ c₁ c₂ lam h : ℕ} (hl : 1 ≤ lam) (hh : h ≤ c₀ * lam ^ 2) (hS : ∑ E ∈ range (4 * h + 1), Partitions.p E ≤ 2 ^ (c₂ * lam)) :
    big h ≤ (2 * lam) ^ (c₁ + 4 + (40 * (c₀ + 1) ^ 2 + c₂)) := by sorry
