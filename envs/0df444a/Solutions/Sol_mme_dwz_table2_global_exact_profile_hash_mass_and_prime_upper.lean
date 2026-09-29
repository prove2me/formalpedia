-- Prove2me | solution 1 for mme_dwz_table2_global_exact_profile_hash_mass_and_prime_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:56:39.555793+00:00
-- url     : https://prove2.me/submissions/f308b5b8-f02e-4a1d-9ca4-551673c96ff0

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_table2_component_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_table2_z_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_common_prime_le_exp_sixteen_length
import Theorems.Thm_mme_dwz_two_branch_common_prime_rate
import Theorems.Thm_mme_dwz_global_behrend_retained_mass_normalization

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem mme_dwz_common_prime_upper_of_positive_degree_mass
    (d p : ℕ) (R : ℝ) (hd : 0 < d)
    (hp : (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R)) :
    (p : ℝ) ≤ 16 * max (d : ℝ) R := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hmax1 : (1 : ℝ) ≤ max (d : ℝ) R :=
    hd1.trans (le_max_left _ _)
  have h8 : (8 : ℝ) ≤ 16 * max (d : ℝ) R := by nlinarith
  simpa [max_eq_right h8] using hp

private theorem mme_dwz_exp_two_branch_eq_retained_rpow_mass (m : ℕ) :
    let L : ℝ := ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)
    let c : ℝ := L * Real.log 2
    Real.exp
        (min
          (c * mme_modern_entropyBits MME.DWZSquare.alpha -
            c * (MME.DWZSquare.maxSameMarginalEntropy -
              mme_modern_entropyBits
                (mme_modern_marginal MME.DWZSquare.shapeX
                  MME.DWZSquare.alpha)))
          (c * mme_modern_entropyBits
                (mme_modern_marginal MME.DWZSquare.shapeZ
                  MME.DWZSquare.alpha) -
            c * MME.DWZSquare.logAlphaP)) =
      Real.rpow 2 (MME.DWZSquare.retainedLogRate * L) := by
  dsimp only
  let L : ℝ := ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)
  let c : ℝ := L * Real.log 2
  let a : ℝ :=
    mme_modern_entropyBits MME.DWZSquare.alpha +
      mme_modern_entropyBits
        (mme_modern_marginal MME.DWZSquare.shapeX MME.DWZSquare.alpha) -
      MME.DWZSquare.maxSameMarginalEntropy
  let b : ℝ :=
    mme_modern_entropyBits
        (mme_modern_marginal MME.DWZSquare.shapeZ MME.DWZSquare.alpha) -
      MME.DWZSquare.logAlphaP
  have hc : 0 ≤ c := mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  have hleft :
      c * mme_modern_entropyBits MME.DWZSquare.alpha -
          c * (MME.DWZSquare.maxSameMarginalEntropy -
            mme_modern_entropyBits
              (mme_modern_marginal MME.DWZSquare.shapeX
                MME.DWZSquare.alpha)) = c * a := by
    dsimp only [a]
    ring
  have hright :
      c * mme_modern_entropyBits
            (mme_modern_marginal MME.DWZSquare.shapeZ
              MME.DWZSquare.alpha) -
          c * MME.DWZSquare.logAlphaP = c * b := by
    dsimp only [b]
    ring
  rw [hleft, hright]
  have hmin : min (c * a) (c * b) = c * min a b := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab, min_eq_left (mul_le_mul_of_nonneg_left hab hc)]
    · rw [min_eq_right hba, min_eq_right (mul_le_mul_of_nonneg_left hba hc)]
  rw [hmin]
  change Real.exp (c * min a b) =
    (2 : ℝ) ^ (MME.DWZSquare.retainedLogRate * L)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold MME.DWZSquare.retainedLogRate
  change Real.exp (c * min a b) =
    Real.exp (Real.log 2 * (min a b * L))
  congr 1
  dsimp only [c]
  ring

/-- Source-facing normalization for a global exact-profile first hash whose
raw output is an arbitrary real aggregate mass, such as a sum of nonhole
fractions. -/
theorem solution
    (m : ℕ) (hm : 0 < m)
    (profileCard fixedTargetCard d Q p : ℕ) (R mass : ℝ)
    (S : Finset ℕ)
    (hprofileCard : profileCard =
      Nat.multinomial Finset.univ
        (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m))
    (hfactor :
      Nat.multinomial Finset.univ
          (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) =
        Nat.multinomial Finset.univ
            (fun k : Fin 5 ↦ MME.DWZTable2Counts.alphaZ k * m) *
          fixedTargetCard)
    (hdpos : 0 < d) (hppos : 0 < p)
    (hd : (d : ℝ) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 5 *
        (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ)) ^ 15 *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            (MME.DWZSquare.maxSameMarginalEntropy -
              mme_modern_entropyBits
                (mme_modern_marginal MME.DWZSquare.shapeX
                  MME.DWZSquare.alpha))))
    (hR : R =
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
        (fixedTargetCard : ℝ) *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            MME.DWZSquare.logAlphaP))
    (hp : (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R))
    (hdPow : d ≤ 15 ^ (MME.DWZTable2Counts.scale * m))
    (hQPow : Q ≤ 15 ^ (MME.DWZTable2Counts.scale * m))
    (hpNat : p ≤ 2 * max 4 (8 * max d Q))
    (hbehrend :
      ((p / 2 : ℕ) : ℝ) *
          Real.exp (-4 * Real.sqrt
            (Real.log (((p / 2 : ℕ) : ℝ)))) ≤
        (S.card : ℝ))
    (hretained :
      ((profileCard : ℝ) * (S.card : ℝ)) /
          (2 * (p : ℝ) ^ 2) ≤ mass) :
    let L := MME.DWZTable2Counts.scale * m
    let x : ℝ := (((L + 1 : ℕ) : ℝ))
    let jointPoly : ℝ := (6 * x) ^ 15
    let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
    let zPoly : ℝ := (6 * x) ^ 5
    let compatibilityPoly : ℝ := (6 * x) ^ 9
    let Dhash : ℝ :=
      32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly)
    (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) ∧
      Real.rpow 2
            (MME.DWZSquare.retainedLogRate * ((L : ℕ) : ℝ)) *
          (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
            Real.exp (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ)))))) /
            Dhash ≤ mass := by
  dsimp only
  let L : ℕ := MME.DWZTable2Counts.scale * m
  let x : ℝ := (((L + 1 : ℕ) : ℝ))
  let jointPoly : ℝ := (6 * x) ^ 15
  let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
  let zPoly : ℝ := (6 * x) ^ 5
  let compatibilityPoly : ℝ := (6 * x) ^ 9
  let Qhash : ℝ :=
    max (jointPoly * degreePoly) (zPoly * compatibilityPoly)
  let Nalpha : ℕ := Nat.multinomial Finset.univ
    (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m)
  let NBZ : ℕ := Nat.multinomial Finset.univ
    (fun k : Fin 5 ↦ MME.DWZTable2Counts.alphaZ k * m)
  let c : ℝ := (L : ℝ) * Real.log 2
  have hretained' :
      ((Nalpha : ℝ) * (S.card : ℝ)) /
          (2 * (p : ℝ) ^ 2) ≤ mass := by
    simpa only [Nalpha, hprofileCard] using hretained
  have hA := mme_dwz_table2_component_multinomial_entropy_polynomial_lower m hm
  have hZ := mme_dwz_table2_z_multinomial_entropy_polynomial_lower m hm
  have hp' := mme_dwz_common_prime_upper_of_positive_degree_mass d p R hdpos hp
  have hbase := mme_dwz_two_branch_common_prime_rate
    Nalpha NBZ fixedTargetCard d p R
    jointPoly degreePoly zPoly compatibilityPoly
    (c * mme_modern_entropyBits MME.DWZSquare.alpha)
    (c * mme_modern_entropyBits
      (mme_modern_marginal MME.DWZSquare.shapeZ MME.DWZSquare.alpha))
    (c * (MME.DWZSquare.maxSameMarginalEntropy -
      mme_modern_entropyBits
        (mme_modern_marginal MME.DWZSquare.shapeX MME.DWZSquare.alpha)))
    (c * MME.DWZSquare.logAlphaP)
    (by simpa only [Nalpha, NBZ] using hfactor) hdpos
    (by dsimp only [jointPoly, x, L]; positivity)
    (by dsimp only [degreePoly, x, L]; positivity)
    (by dsimp only [zPoly, x, L]; positivity)
    (by dsimp only [compatibilityPoly, x, L]; positivity)
    (by simpa only [Nalpha, jointPoly, x, c, L, Nat.cast_mul,
      mul_comm (m : ℝ) (MME.DWZTable2Counts.scale : ℝ)] using hA)
    (by simpa only [NBZ, zPoly, x, c, L, Nat.cast_mul,
      mul_comm (m : ℝ) (MME.DWZTable2Counts.scale : ℝ)] using hZ)
    (by simpa only [degreePoly, x, c, L, Nat.cast_mul,
      mul_comm (m : ℝ) (MME.DWZTable2Counts.scale : ℝ)] using hd)
    (by simpa only [compatibilityPoly, x, c, L, Nat.cast_mul,
      mul_comm (m : ℝ) (MME.DWZTable2Counts.scale : ℝ)] using hR)
    hp'
  rw [mme_dwz_exp_two_branch_eq_retained_rpow_mass m] at hbase
  have hprime :
      (p : ℝ) * Real.rpow 2
          (MME.DWZSquare.retainedLogRate * (L : ℝ)) ≤
        16 * Qhash * (Nalpha : ℝ) := by
    simpa only [Qhash] using hbase
  have hQpos : 0 < Qhash := by
    dsimp only [Qhash, jointPoly, degreePoly, zPoly, compatibilityPoly, x, L]
    positivity
  have hmass := mme_dwz_global_behrend_retained_mass_normalization
    p Nalpha S
      (Real.rpow 2 (MME.DWZSquare.retainedLogRate * (L : ℝ))) Qhash mass
      hppos hQpos hprime hbehrend hretained'
  have hpExp := mme_dwz_common_prime_le_exp_sixteen_length
    L d Q p (by simpa only [L] using hdPow)
      (by simpa only [L] using hQPow) hpNat
  refine ⟨hpExp, ?_⟩
  simpa only [Qhash, L, jointPoly, degreePoly, zPoly,
    compatibilityPoly, x] using hmass
