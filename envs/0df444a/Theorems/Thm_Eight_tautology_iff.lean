-- Prove2me | Theorems.Thm_Eight_tautology_iff
-- name    : Eight.tautology_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:31:35.626375+00:00
-- url     : https://prove2.me/theorems/cb9bf785-8566-48b1-a151-e54237b64000
-- title:
--   Eight: tautology iff
-- statement:
--   «A k-DNF is a tautology exactly if its negation, a k-CNF, is unsatisfiable», in this form: the
--   DNF ψ is a tautology exactly if the CNF with the same lists of literals is unsatisfiable. An
--   assignment a falsifies the DNF exactly if the
--   assignment with all values negated satisfies the CNF.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/NSETH.lean#L45-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/NSETH.lean#L45-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_NSETHDefs
import Definitions.Def_Eight_Cor_Defs
import Definitions.Def_Eight_Level_End
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_KSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_WidthK_Top_EndLemmas
import Definitions.Def_WidthK_Decode
import Definitions.Def_SparsifyWidthK_DefsProg
import Definitions.Def_GraphProblems_Host
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_NSETH
set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog Paper Turing

theorem Eight.tautology_iff {n : ℕ} (ψ : DNF n) : Tautology ψ ↔ ¬ Sat3.Satisfiable ψ := by sorry
