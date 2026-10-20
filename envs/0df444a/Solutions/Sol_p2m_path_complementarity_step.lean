-- Prove2me | solution 1 for p2m_path_complementarity_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:13:39.297213+00:00
-- url     : https://prove2.me/submissions/5777d633-13a4-4c6b-865a-e8c08123d3ed

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_path_sum_complementarity
import Theorems.Thm_p2m_path_barrierParam_identity
import Theorems.Thm_p2m_complementarity_advance_expansion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
open scoped VanderbeiLP.PathFollowing in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (δ r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r)
    (hr1 : r < 1) (p d p' : PDPoint m n) (hstep : IsPathFollowingStep A b c δ r p d p')
    (M : ℝ) (hx : normInf p.x ≤ M) (hy : normInf p.y ≤ M) :
    complementarity p' ≤
      (1 - (1 - δ) * stepLength r p d) * complementarity p
        + M * norm1 (primalInfeas A b p) + M * norm1 (dualInfeas A c p) := by
  classical
  letI : LE ℝ := Real.instPreorder.toLE
  rcases hstep with ⟨hp, hdir, hnext⟩
  rcases hdir with ⟨hρ, hσ, hcompx, hcompw⟩
  subst p'
  set θ := stepLength r p d
  have abs_le_normInf {k : ℕ} (v : Fin k → ℝ) (i : Fin k) :
      @LE.le ℝ Real.instPreorder.toLE |v i| (normInf v) := by
    unfold normInf
    exact le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)
  have normInf_nonneg_local {k : ℕ} (v : Fin k → ℝ) : 0 ≤ normInf v := by
    cases k with
    | zero => simp [normInf]
    | succ k => exact le_trans (abs_nonneg (v 0)) (abs_le_normInf v 0)
  have hR_nonneg : 0 ≤ maxAbsRatio p d := by
    unfold maxAbsRatio
    exact le_trans (normInf_nonneg_local _)
      (le_max_of_le_left (le_max_of_le_left le_rfl))
  have hθ0 : 0 ≤ θ := by
    dsimp [θ, stepLength]; split_ifs with hR
    · norm_num
    · have hRpos : 0 < maxAbsRatio p d := lt_of_le_of_ne hR_nonneg (Ne.symm hR)
      exact le_min (div_nonneg (le_of_lt hr0) (le_of_lt hRpos)) (by norm_num)
  have hθ1 : θ ≤ 1 := by
    dsimp [θ, stepLength]; split_ifs with hR
    · norm_num
    · exact min_le_right _ _
  have hcross : d.y ⬝ᵥ primalInfeas A b p - d.x ⬝ᵥ dualInfeas A c p =
      d.y ⬝ᵥ d.w + d.z ⬝ᵥ d.x := by
    rw [← hρ, ← hσ]; simp only [dotProduct_add, dotProduct_sub]; rw [Matrix.dotProduct_transpose_mulVec]; simp [dotProduct_comm]
  rcases hp with ⟨hpx, hpw, hpy, hpz⟩
  have hθR : θ * maxAbsRatio p d ≤ r := by
    by_cases hR : maxAbsRatio p d = 0
    · simp [θ, stepLength, hR]
      exact le_of_lt hr0
    · have hRpos : 0 < maxAbsRatio p d := lt_of_le_of_ne hR_nonneg (Ne.symm hR)
      by_cases hq : r / maxAbsRatio p d ≤ 1
      · have hcancel : r / maxAbsRatio p d * maxAbsRatio p d = r :=
          div_mul_cancel₀ r (ne_of_gt hRpos)
        simp [θ, stepLength, hR, min_eq_left hq, hcancel]
      · have hq' : 1 < r / maxAbsRatio p d := lt_of_not_ge hq
        have hRlt : maxAbsRatio p d < r := by simpa using (lt_div_iff₀ hRpos).mp hq'
        simpa [θ, stepLength, hR, min_eq_right (le_of_lt hq')] using le_of_lt hRlt
  have hratiox (j : Fin n) : |d.x j / p.x j| ≤ maxAbsRatio p d := by
    unfold maxAbsRatio
    exact le_trans (abs_le_normInf (fun j => d.x j / p.x j) j)
      (le_max_of_le_left (le_max_of_le_left le_rfl))
  have hratioy (i : Fin m) : |d.y i / p.y i| ≤ maxAbsRatio p d := by
    unfold maxAbsRatio
    exact le_trans (abs_le_normInf (fun i => d.y i / p.y i) i)
      (le_max_of_le_right (le_max_of_le_left le_rfl))
  have hdirx (j : Fin n) : |d.x j| ≤ maxAbsRatio p d * p.x j :=
    (div_le_iff₀ (hpx j)).mp (by simpa [abs_div, abs_of_pos (hpx j)] using hratiox j)
  have hdiry (i : Fin m) : |d.y i| ≤ maxAbsRatio p d * p.y i :=
    (div_le_iff₀ (hpy i)).mp (by simpa [abs_div, abs_of_pos (hpy i)] using hratioy i)
  have hstepx (j : Fin n) : θ * |d.x j| ≤ r * p.x j := by
    calc θ * |d.x j| ≤ θ * (maxAbsRatio p d * p.x j) := mul_le_mul_of_nonneg_left (hdirx j) hθ0
      _ = (θ * maxAbsRatio p d) * p.x j := by ring
      _ ≤ r * p.x j := mul_le_mul_of_nonneg_right hθR (le_of_lt (hpx j))
  have hstepy (i : Fin m) : θ * |d.y i| ≤ r * p.y i := by
    calc θ * |d.y i| ≤ θ * (maxAbsRatio p d * p.y i) := mul_le_mul_of_nonneg_left (hdiry i) hθ0
      _ = (θ * maxAbsRatio p d) * p.y i := by ring
      _ ≤ r * p.y i := mul_le_mul_of_nonneg_right hθR (le_of_lt (hpy i))
  have hboundx (j : Fin n) : p.x j ≤ M := by
    calc p.x j ≤ |p.x j| := le_abs_self _
      _ ≤ normInf p.x := by
        exact abs_le_normInf p.x j
      _ ≤ M := hx
  have hboundy (i : Fin m) : p.y i ≤ M := by
    calc p.y i ≤ |p.y i| := le_abs_self _
      _ ≤ normInf p.y := by
        exact abs_le_normInf p.y i
      _ ≤ M := hy
  have hresy (i : Fin m) : θ ^ 2 * (d.y i * primalInfeas A b p i) ≤
      M * |primalInfeas A b p i| := by
    have hpstep : r * p.y i ≤ M := by nlinarith [hr1, hpy i, hboundy i]
    calc θ ^ 2 * (d.y i * primalInfeas A b p i) ≤ θ ^ 2 * (|d.y i| * |primalInfeas A b p i|) :=
          mul_le_mul_of_nonneg_left (by rw [← abs_mul]; exact le_abs_self _) (sq_nonneg θ)
      _ = (θ * |d.y i|) * (θ * |primalInfeas A b p i|) := by ring
      _ ≤ (r * p.y i) * |primalInfeas A b p i| :=
        mul_le_mul (hstepy i) (by simpa using mul_le_mul_of_nonneg_right hθ1 (abs_nonneg _))
          (mul_nonneg hθ0 (abs_nonneg _)) (mul_nonneg (le_of_lt hr0) (le_of_lt (hpy i)))
      _ ≤ M * |primalInfeas A b p i| := mul_le_mul_of_nonneg_right hpstep (abs_nonneg _)
  have hresx (j : Fin n) : θ ^ 2 * (-(d.x j * dualInfeas A c p j)) ≤
      M * |dualInfeas A c p j| := by
    have hpstep : r * p.x j ≤ M := by nlinarith [hr1, hpx j, hboundx j]
    calc θ ^ 2 * (-(d.x j * dualInfeas A c p j)) ≤ θ ^ 2 * (|d.x j| * |dualInfeas A c p j|) :=
          mul_le_mul_of_nonneg_left (by rw [← abs_mul]; exact neg_le_abs _) (sq_nonneg θ)
      _ = (θ * |d.x j|) * (θ * |dualInfeas A c p j|) := by ring
      _ ≤ (r * p.x j) * |dualInfeas A c p j| :=
        mul_le_mul (hstepx j) (by simpa using mul_le_mul_of_nonneg_right hθ1 (abs_nonneg _))
          (mul_nonneg hθ0 (abs_nonneg _)) (mul_nonneg (le_of_lt hr0) (le_of_lt (hpx j)))
      _ ≤ M * |dualInfeas A c p j| := mul_le_mul_of_nonneg_right hpstep (abs_nonneg _)
  have hresY : θ ^ 2 * (d.y ⬝ᵥ primalInfeas A b p) ≤ M * norm1 (primalInfeas A b p) := by
    simp only [dotProduct, norm1]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hresy i)
  have hresX : θ ^ 2 * (-(d.x ⬝ᵥ dualInfeas A c p)) ≤ M * norm1 (dualInfeas A c p) := by
    simp only [dotProduct, norm1]
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hresx j)
  let μ := barrierParam δ p
  have hsumx := p2m_path_sum_complementarity p.x p.z d.x d.z μ hcompx
  have hsumw := p2m_path_sum_complementarity p.y p.w d.y d.w μ hcompw
  have hbar : ((n : ℝ) + m) * μ = δ * complementarity p := by
    simpa [μ] using p2m_path_barrierParam_identity δ p
  have hexp0 := p2m_complementarity_advance_expansion p d θ
  have hexp : complementarity (p.advance θ d) = complementarity p +
      θ * ((n : ℝ) * μ + (m : ℝ) * μ - complementarity p) +
      θ ^ 2 * (d.y ⬝ᵥ primalInfeas A b p - d.x ⬝ᵥ dualInfeas A c p) := by
    calc
      _ = complementarity p + θ * ((∑ j : Fin n, (p.z j * d.x j + p.x j * d.z j)) +
          (∑ i : Fin m, (p.w i * d.y i + p.y i * d.w i))) +
          θ ^ 2 * (d.z ⬝ᵥ d.x + d.y ⬝ᵥ d.w) := hexp0
      _ = _ := by
        have hcross' : d.y ⬝ᵥ primalInfeas A b p - d.x ⬝ᵥ dualInfeas A c p =
            d.z ⬝ᵥ d.x + d.y ⬝ᵥ d.w := by simpa [add_comm] using hcross
        rw [hsumx, hsumw, ← hcross']
        simp only [complementarity, dotProduct_comm]
        ring_nf
  have hcontract : complementarity p + θ * ((n : ℝ) * μ + (m : ℝ) * μ -
      complementarity p) = (1 - (1 - δ) * θ) * complementarity p := by
    rw [← add_mul, hbar]
    ring
  rw [hexp, hcontract]
  nlinarith [hresY, hresX]
end
