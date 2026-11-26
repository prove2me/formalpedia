-- Prove2me | solution 1 for natDegree_divByMonic_X_sub_C_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:24.660466+00:00
-- url     : https://prove2.me/submissions/4b030d3f-f076-4222-beba-b67d5fd956e2

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_natDegree_divByMonic_X_sub_C_eq_sub_one

set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (p : Polynomial ℂ) (xi : ℂ) (hp : 0 < p.natDegree) :
    (p /ₘ (Polynomial.X - Polynomial.C xi)).natDegree < p.natDegree := by
  rw [natDegree_divByMonic_X_sub_C_eq_sub_one]
  omega
