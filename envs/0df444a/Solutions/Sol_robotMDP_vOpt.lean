-- Prove2me | solution 1 for robotMDP_vOpt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:41:33.091016+00:00
-- url     : https://prove2.me/submissions/aea7c55e-60cf-415f-a1b2-e8b7a31c67e3

import Definitions.Def_Mdp_PolicyIteration
import Definitions.Def_Mdp_RecyclingRobot
import Theorems.Thm_Mdp_DiscountedMDP_contractingWith_bellman

section
open Mdp Mdp.DiscountedMDP
private theorem toReal_searchPMF (s' : RobotState) : (searchPMF s').toReal = 1 / 2 := by
  unfold searchPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (by norm_num)
private theorem toReal_pure_high_high :
    (PMF.pure RobotState.high RobotState.high).toReal = 1 := by
  simp [PMF.pure_apply]
private theorem toReal_pure_high_low :
    (PMF.pure RobotState.high RobotState.low).toReal = 0 := by
  simp [PMF.pure_apply]
private theorem toReal_pure_low_low :
    (PMF.pure RobotState.low RobotState.low).toReal = 1 := by
  simp [PMF.pure_apply]
private theorem toReal_pure_low_high :
    (PMF.pure RobotState.low RobotState.high).toReal = 0 := by
  simp [PMF.pure_apply]
private theorem expect_high_search : robotMDP.expect .high .search robotV0 = 8 / 3 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.high RobotAction.search s').toReal * robotV0 s'
    = 8 / 3
  rw [robotState_sum]
  simp only [robotK, toReal_searchPMF, robotV0]
  norm_num
private theorem expect_high_wait : robotMDP.expect .high .wait robotV0 = 10 / 3 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.high RobotAction.wait s').toReal * robotV0 s'
    = 10 / 3
  rw [robotState_sum]
  simp only [robotK, toReal_pure_high_high, toReal_pure_high_low, robotV0]
  norm_num
private theorem expect_high_recharge : robotMDP.expect .high .recharge robotV0 = 10 / 3 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.high RobotAction.recharge s').toReal * robotV0 s'
    = 10 / 3
  rw [robotState_sum]
  simp only [robotK, toReal_pure_high_high, toReal_pure_high_low, robotV0]
  norm_num
private theorem expect_low_search : robotMDP.expect .low .search robotV0 = 8 / 3 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.low RobotAction.search s').toReal * robotV0 s'
    = 8 / 3
  rw [robotState_sum]
  simp only [robotK, toReal_searchPMF, robotV0]
  norm_num
private theorem expect_low_wait : robotMDP.expect .low .wait robotV0 = 2 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.low RobotAction.wait s').toReal * robotV0 s' = 2
  rw [robotState_sum]
  simp only [robotK, toReal_pure_low_low, toReal_pure_low_high, robotV0]
  norm_num
private theorem expect_low_recharge : robotMDP.expect .low .recharge robotV0 = 10 / 3 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.low RobotAction.recharge s').toReal * robotV0 s'
    = 10 / 3
  rw [robotState_sum]
  simp only [robotK, toReal_pure_high_high, toReal_pure_high_low, robotV0]
  norm_num
end

set_option autoImplicit true
open Mdp Mdp.DiscountedMDP
theorem _root_.solution : robotMDP.vOpt = robotV0 := by
  refine (robotMDP.contractingWith_bellman.fixedPoint_unique ?_).symm
  funext s
  unfold DiscountedMDP.bellman
  cases s with
  | high =>
      apply le_antisymm
      · rw [Finset.sup'_le_iff]
        rintro a -
        cases a with
        | search =>
            rw [expect_high_search]
            simp only [robotR, robotMDP, robotV0]
            norm_num
        | wait =>
            rw [expect_high_wait]
            simp only [robotR, robotMDP, robotV0]
            norm_num
        | recharge =>
            rw [expect_high_recharge]
            simp only [robotR, robotMDP, robotV0]
            norm_num
      · have hle := Finset.le_sup'
          (fun a => robotR RobotState.high a
            + robotMDP.l * robotMDP.expect RobotState.high a robotV0)
          (Finset.mem_univ RobotAction.search)
        rw [expect_high_search] at hle
        simp only [robotR, robotMDP, robotV0] at hle ⊢
        linarith [hle]
  | low =>
      apply le_antisymm
      · rw [Finset.sup'_le_iff]
        rintro a -
        cases a with
        | search =>
            rw [expect_low_search]
            simp only [robotR, robotMDP, robotV0]
            norm_num
        | wait =>
            rw [expect_low_wait]
            simp only [robotR, robotMDP, robotV0]
            norm_num
        | recharge =>
            rw [expect_low_recharge]
            simp only [robotR, robotMDP, robotV0]
            norm_num
      · have hle := Finset.le_sup'
          (fun a => robotR RobotState.low a
            + robotMDP.l * robotMDP.expect RobotState.low a robotV0)
          (Finset.mem_univ RobotAction.wait)
        rw [expect_low_wait] at hle
        simp only [robotR, robotMDP, robotV0] at hle ⊢
        linarith [hle]
