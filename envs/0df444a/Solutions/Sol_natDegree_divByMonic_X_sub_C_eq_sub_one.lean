-- Prove2me | solution 1 for natDegree_divByMonic_X_sub_C_eq_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:21.943289+00:00
-- url     : https://prove2.me/submissions/5428d7d4-882a-4180-84b6-c380d1b7f0f7

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound

set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (p : Polynomial ℂ) (xi : ℂ) :
    (p /ₘ (Polynomial.X - Polynomial.C xi)).natDegree =
      p.natDegree - 1 := by
  rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C xi),
    Polynomial.natDegree_X_sub_C]
