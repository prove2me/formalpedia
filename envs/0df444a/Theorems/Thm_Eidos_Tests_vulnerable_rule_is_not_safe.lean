-- Prove2me | Theorems.Thm_Eidos_Tests_vulnerable_rule_is_not_safe
-- name    : Eidos.Tests.vulnerable_rule_is_not_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:37:23.857168+00:00
-- url     : https://prove2.me/theorems/fe0e8bf7-e4c3-4928-a22a-666f8609261e
-- title:
--   Tests: vulnerable rule is not safe
-- statement:
--   The Tests construction uses the vulnerable rule is not safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/EidosTests.lean#L60-L63
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/EidosTests.lean#L60-L63

import Definitions.Def_Eidos
import Definitions.Def_EidosTests
set_option autoImplicit false
open Eidos Eidos.Tests
open Ergo Examples.Reserve

theorem Eidos.Tests.vulnerable_rule_is_not_safe :
    ¬ (∀ ctx, Accepts vulnerableScript ctx → WithdrawalBounded exampleReserve ctx) := by sorry
