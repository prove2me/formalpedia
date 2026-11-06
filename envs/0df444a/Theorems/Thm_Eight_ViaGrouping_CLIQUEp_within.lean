-- Prove2me | Theorems.Thm_Eight_ViaGrouping_CLIQUEp_within
-- name    : Eight.ViaGrouping.CLIQUEp_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:23:44.660981+00:00
-- url     : https://prove2.me/theorems/b49b4145-d8b4-42db-b472-35fd68f58371
-- title:
--   Via Grouping: CLIQUEp within
-- statement:
--   CLIQUE(ℓ) returns the value of every (K_ℓ, λ)-clique within C · 2^{e_ℓ K_ℓ² λ} (B + λ)^C steps,
--   times the cost of a query, with the e_ℓ of Section 8 for ρ = 11/12. The numbers are those of the
--   paper. Level 0 is brute force; the step from ℓ to ℓ + 1 is Lemma 1 for
--   the algorithm of its proof, then one level.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Alg.lean#L67-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Alg.lean#L67-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_Alg
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.CLIQUEp_within (ℓ : ℕ) : (CLIQUEp ℓ).Within (levelK ℓ) (Level.levelE ℓ) := by sorry
