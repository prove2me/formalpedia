-- Prove2me | solution 1 for p2m_complementarity_advance_expansion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:50:19.417105+00:00
-- url     : https://prove2.me/submissions/111386a4-95da-4592-b3bc-56a28de64c0e

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_sum_complementarity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
theorem solution {m n : ℕ}
    (p d : PDPoint m n) (θ : ℝ) :
    complementarity (p.advance θ d) = complementarity p +
      θ * ((∑ j : Fin n, (p.z j * d.x j + p.x j * d.z j)) +
        (∑ i : Fin m, (p.w i * d.y i + p.y i * d.w i))) +
      θ ^ 2 * (d.z ⬝ᵥ d.x + d.y ⬝ᵥ d.w) := by
  classical
  have sum_product_expand {k : ℕ} (a b c e : Fin k → ℝ) :
      (∑ i : Fin k, (a i + θ * c i) * (b i + θ * e i)) =
        (∑ i, a i * b i) + θ * ((∑ i, a i * e i) + (∑ i, b i * c i)) +
          θ ^ 2 * (∑ i, c i * e i) := by
    calc
      _ = ∑ i : Fin k,
          (a i * b i + θ * (a i * e i + b i * c i) + θ ^ 2 * (c i * e i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  have hprodx :
      (p.z + θ • d.z) ⬝ᵥ (p.x + θ • d.x) =
        p.z ⬝ᵥ p.x + θ * (p.z ⬝ᵥ d.x + p.x ⬝ᵥ d.z) +
          θ ^ 2 * (d.z ⬝ᵥ d.x) := by
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_product_expand p.z p.x d.z d.x
  have hprodw :
      (p.y + θ • d.y) ⬝ᵥ (p.w + θ • d.w) =
        p.y ⬝ᵥ p.w + θ * (p.y ⬝ᵥ d.w + p.w ⬝ᵥ d.y) +
          θ ^ 2 * (d.y ⬝ᵥ d.w) := by
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_product_expand p.y p.w d.y d.w
  simp only [complementarity, PDPoint.advance]
  rw [hprodx, hprodw]
  simp only [dotProduct]
  simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  ring
