-- Prove2me | Theorems.Thm_ActuarialValuation_ulMixed_equal_basis
-- name    : ActuarialValuation.ulMixed_equal_basis
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:34:49.128985+00:00
-- url     : https://prove2.me/theorems/4b1cd172-4171-452f-be30-743821f7b822
-- title:
--   Monthly account premium expenses and insurance charges: ulMixed_equal_basis
-- statement:
--   The mixed-rate reserve recursion reduces to the conventional end-period insurance charge when both rate bases agree.
--
--   Mathematical relation:
--
--   $$
--   ulMixed\_equal\_basis
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulMixedNext

namespace ActuarialValuation

theorem ulMixed_equal_basis (earned interest mortality risk : ℝ) (hi : 1+interest ≠ 0) : ulMixedNext earned interest interest mortality risk = earned-mortality*risk := by sorry

end ActuarialValuation
