-- Prove2me | Theorems.Thm_Exits_two_le_levelK
-- name    : Exits.two_le_levelK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:33:02.182641+00:00
-- url     : https://prove2.me/theorems/32f926ee-1b80-4d6c-aef3-a5cc37eb6037
-- title:
--   Exits: two le level K
-- statement:
--   K_ℓ ≥ 2 (Section 8: «K₀ = 64 … K_{ℓ+1} = g_ℓ² = 9K_ℓ¹⁶»).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Level.lean#L39-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Level.lean#L39-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_SecLevel_EStar
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic.Ring
import Definitions.Def_Exits_Level
set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Paper Eight Eight.SecNetworks Eight.ViaGrouping

theorem Exits.two_le_levelK (ℓ : ℕ) : 2 ≤ levelK ℓ := by sorry
