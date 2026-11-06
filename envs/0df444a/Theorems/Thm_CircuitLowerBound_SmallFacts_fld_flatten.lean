-- Prove2me | Theorems.Thm_CircuitLowerBound_SmallFacts_fld_flatten
-- name    : CircuitLowerBound.SmallFacts.fld_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:42:27.68189+00:00
-- url     : https://prove2.me/theorems/a96f894c-f200-43aa-ae39-f44401053b41
-- title:
--   Small Facts: fld flatten
-- statement:
--   The i-th number of W bits in a word that begins with numbers of W bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L123-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L123-L139

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.SmallFacts

theorem CircuitLowerBound.SmallFacts.fld_flatten (W : ℕ) (r : List Bool) : ∀ (X : List ℕ), (∀ x ∈ X, x < 2 ^ W) → ∀ i, i < X.length →
    fld W ((X.map (toWord W)).flatten ++ r) i = X.getD i 0
  := by sorry
