-- Prove2me | solution 1 for many_eligibleDeviations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:06.216961+00:00
-- url     : https://prove2.me/submissions/c963956d-bef5-4cf5-add9-fdbdf118d6e7

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_natCard_validDeviation
public import Theorems.Thm_card_exceptionalDeviations_le
public import Theorems.Thm_DegreeEligibleArithmetic_four_mul_card_eligible_ge
public import Theorems.Thm_card_startBoundary_le
public import Theorems.Thm_card_finishBoundary_le
public import Theorems.Thm_sum_returnLength_le_d_mul_card

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
theorem _root_.solution (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    k ≤ 4 * (eligibleDeviations d G hG start rho).card := by
  let n := Fintype.card V
  let L := degreeCutoff d n k
  have hnpos : 0 < n := by omega
  have hkpos : 0 < k := by
    have hdpos : 0 < d := by omega
    have hcoef : 0 < 1048576 * d ^ 2 * n := by positivity
    nlinarith [hhigh]
  have hk : 2 ≤ k := by
    have hbase : 4 ≤ 1048576 * d ^ 2 * n := by
      have : 1 ≤ n := hnpos
      nlinarith
    nlinarith [hhigh]
  have hcardI : k - 1 ≤
      (Finset.univ : Finset (ValidDeviation d G hG start rho.1 k)).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      natCard_validDeviation d G hG start rho.1 k]
    have : 1 ≤ d - 2 := by omega
    nlinarith
  have hsum :
      ∑ q ∈ (Finset.univ : Finset (ValidDeviation d G hG start rho.1 k)),
          returnLength d G hG start rho.1 k q ≤ d * n := by
    simpa [n] using sum_returnLength_le_d_mul_card d G hG start rho
  have hlongScale : 16 * (d * n) ≤ k * (L + 1) := by
    have hlt : 64 * d * n < k * L := by
      simpa [L, degreeCutoff] using Nat.lt_mul_div_succ (64 * d * n) hkpos
    nlinarith
  have hdiv : (64 * d * n / k) * k ≤ 64 * d * n :=
    Nat.div_mul_le_self _ _
  have hboundaryMul : (16 * (L * d)) * k ≤ k * k := by
    calc
      (16 * (L * d)) * k =
          16 * d * ((64 * d * n / k) * k + k) := by
            dsimp [L, degreeCutoff]
            ring
      _ ≤ 16 * d * (64 * d * n + n) := by
        gcongr
      _ ≤ 1048576 * d ^ 2 * n := by
        calc
          16 * d * (64 * d * n + n) =
              1024 * d ^ 2 * n + 16 * d * n := by ring
          _ ≤ 1024 * d ^ 2 * n + 16 * d ^ 2 * n := by
            gcongr
            nlinarith
          _ = 1040 * (d ^ 2 * n) := by ring
          _ ≤ 1048576 * (d ^ 2 * n) := by gcongr <;> omega
          _ = 1048576 * d ^ 2 * n := by ring
      _ ≤ k ^ 2 := hhigh
      _ = k * k := by ring
  have hboundaryScale : 16 * (L * d) ≤ k :=
    Nat.le_of_mul_le_mul_right hboundaryMul hkpos
  have hexceptionScale : 64 * d ≤ k := by
    have hsmall : (64 * d) ^ 2 ≤ 1048576 * d ^ 2 * n := by
      have hc : 4096 ≤ 1048576 * n := by nlinarith
      calc
        (64 * d) ^ 2 = 4096 * d ^ 2 := by ring
        _ ≤ (1048576 * n) * d ^ 2 := Nat.mul_le_mul_right (d ^ 2) hc
        _ = 1048576 * d ^ 2 * n := by ring
    nlinarith [hsmall, hhigh]
  apply DegreeEligibleArithmetic.four_mul_card_eligible_ge
    (n := n) (k := k) (d := d) (L := L)
    (I := Finset.univ)
    (X := exceptionalDeviations d G hG start rho)
    (c := returnLength d G hG start rho.1 k)
    (r := deviationStartTime d G hG start rho)
    (j := deviationFinishTime d G hG start rho)
  · exact hk
  · exact hcardI
  · exact hsum
  · exact card_exceptionalDeviations_le d G hG start rho
  · exact card_startBoundary_le d G hG start rho L
  · exact card_finishBoundary_le d G hG start rho L
  · exact hlongScale
  · exact hboundaryScale
  · exact hexceptionScale
