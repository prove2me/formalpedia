-- Prove2me | Theorems.Thm_BKAR_Forest_localBoundarySupportOrderContribution_eq_zero_of_length_ne
-- name    : BKAR.Forest.localBoundarySupportOrderContribution_eq_zero_of_length_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:55.674801+00:00
-- url     : https://prove2.me/theorems/fed13ba6-413d-4101-b7f6-828544fc388b
-- title:
--   Forest: local Boundary Support Order Contribution eq zero of length ne
-- statement:
--   A local support/order boundary sector can contribute only when the requested
--   order is obtained by appending exactly one edge to the current prefix.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L156-L171
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L156-L171

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.localBoundarySupportOrderContribution_eq_zero_of_length_ne
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (hne : order.length ≠ pref.length + 1) :
    localBoundarySupportOrderContribution choices F pref prefixTs top
        I order ρ = 0 := by sorry
