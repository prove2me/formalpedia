-- Prove2me | solution 1 for mme_dwz_q6_112_Z_decoder_pair_and_leftGrade
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T07:12:53.982108+00:00
-- url     : https://prove2.me/submissions/4db01af3-5714-42ff-acf8-dcab98439202

import Definitions.Def_mme_dwz_q6_112_coupled_profile_data

open MME

universe u


set_option autoImplicit false
set_option maxHeartbeats 400000

open MME.DWZComponentRestriction

/-- The q=6 Z-coordinate decoder is inverse to the literal canonical pair
label and translates the canonical left split grade to the coupled grade. -/
theorem solution
    (p : LiftedCoarsePair.{u} 6 2) :
    dwzCanonical112Pair 6 2 (dwzQ6Canonical112ZCoord p) = p.down.1 ∧
    p.leftGrade =
      mme_dwz_q6_coupled_Z_leftGrade
        (dwzQ6CoupledCoordGrade 2 (dwzQ6Canonical112ZCoord p)) := by
  have hgrade := congrArg Fin.val p.down.2
  have hp :
      dwzCanonical112Pair 6 2 (dwzQ6Canonical112ZCoord p) =
        p.down.1 := by
    have ha8 : p.down.1.1.val < 8 := p.down.1.1.isLt
    have hb8 : p.down.1.2.val < 8 := p.down.1.2.isLt
    by_cases haT : p.down.1.1.val = 7
    · have hz : dwzQ6Canonical112ZCoord p = Sum.inl 0 := by
        unfold dwzQ6Canonical112ZCoord
        dsimp only
        exact dif_pos haT
      rw [hz]
      have hbO : p.down.1.2.val = 0 := by
        by_contra hbO
        by_cases hbT : p.down.1.2.val = 7
        · simp [cwSquarePairGrade, cwSquareCoordGrade, haT, hbT]
            at hgrade
        · simp [cwSquarePairGrade, cwSquareCoordGrade, haT, hbO, hbT]
            at hgrade
      apply Prod.ext <;> apply Fin.ext
      · change 7 = p.down.1.1.val
        exact haT.symm
      · change 0 = p.down.1.2.val
        exact hbO.symm
    · by_cases haO : p.down.1.1.val = 0
      · have hz : dwzQ6Canonical112ZCoord p = Sum.inl 1 := by
          unfold dwzQ6Canonical112ZCoord
          dsimp only
          exact (dif_neg haT).trans (dif_pos haO)
        rw [hz]
        have hbT : p.down.1.2.val = 7 := by
          by_contra hbT
          by_cases hbO : p.down.1.2.val = 0
          · simp [cwSquarePairGrade, cwSquareCoordGrade, haO, hbO]
              at hgrade
          · simp [cwSquarePairGrade, cwSquareCoordGrade, haO, hbO, hbT]
              at hgrade
        apply Prod.ext <;> apply Fin.ext
        · change 0 = p.down.1.1.val
          exact haO.symm
        · change 7 = p.down.1.2.val
          exact hbT.symm
      · have hbO : p.down.1.2.val ≠ 0 := by
          intro hbO
          simp [cwSquarePairGrade, cwSquareCoordGrade, haT, haO, hbO]
            at hgrade
        have hbT : p.down.1.2.val ≠ 7 := by
          intro hbT
          simp [cwSquarePairGrade, cwSquareCoordGrade, haT, haO, hbT]
            at hgrade
        have haLt : p.down.1.1.val - 1 < 6 := by omega
        have hbLt : p.down.1.2.val - 1 < 6 := by omega
        have hz : dwzQ6Canonical112ZCoord p =
            Sum.inr (⟨p.down.1.2.val - 1, hbLt⟩,
              ⟨p.down.1.1.val - 1, haLt⟩) := by
          unfold dwzQ6Canonical112ZCoord
          dsimp only
          exact (dif_neg haT).trans (dif_neg haO)
        rw [hz]
        apply Prod.ext <;> apply Fin.ext
        · change p.down.1.1.val - 1 + 1 = p.down.1.1.val
          omega
        · change p.down.1.2.val - 1 + 1 = p.down.1.2.val
          omega
  refine ⟨hp, ?_⟩
  let c := dwzQ6Canonical112ZCoord p
  change cwSquareCoordGrade 6 p.down.1.1 = _
  rw [← hp]
  change cwSquareCoordGrade 6 (dwzCanonical112Pair 6 2 c).1 =
    mme_dwz_q6_coupled_Z_leftGrade (dwzQ6CoupledCoordGrade 2 c)
  rcases c with a | ij
  · fin_cases a <;> rfl
  · rcases ij with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> rfl
