-- Prove2me | solution 1 for flt5_ck5_norm_nonneg
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T17:06:41.551256+00:00
-- url     : https://prove2.me/submissions/46099d40-3b41-4a56-805e-40704ede7d15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Norm.Transitivity
import Theorems.Thm_flt5_ck5_prod_emb_nonneg

-- Proof that Algebra.norm ℚ x ≥ 0 for x : CyclotomicField 5 ℚ.
-- Strategy (via complex embeddings and conjugate pairing):
-- 1. Algebra.norm_eq_prod_embeddings ℚ ℂ x:
--    algebraMap ℚ ℂ (norm ℚ x) = ∏ σ : CK5 →ₐ[ℚ] ℂ, σ x
-- 2. Child flt5_ck5_prod_emb_nonneg: 0 ≤ (∏ σ, σ x).re
--    (totally imaginary field: conjugate pairing gives normSq values ≥ 0)
-- 3. (algebraMap ℚ ℂ q).re = q as real → combine to get norm ≥ 0.

noncomputable section

abbrev CK5nk := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5nk :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5nk :=
  IsCyclotomicExtension.numberField {5} ℚ CK5nk

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution (x : CK5nk) : 0 ≤ Algebra.norm ℚ x := by
  -- Step 1: norm = product of all complex embeddings
  have hprod : algebraMap ℚ ℂ (Algebra.norm ℚ x) =
      ∏ σ : CK5nk →ₐ[ℚ] ℂ, σ x :=
    Algebra.norm_eq_prod_embeddings ℚ ℂ x
  -- Step 2: child theorem: product has nonneg real part
  have hnneg : 0 ≤ (∏ σ : CK5nk →ₐ[ℚ] ℂ, σ x).re :=
    flt5_ck5_prod_emb_nonneg x
  -- Step 3: (algebraMap ℚ ℂ q).re = q, so connect product back to norm
  have hre : (algebraMap ℚ ℂ (Algebra.norm ℚ x)).re = (Algebra.norm ℚ x : ℝ) := by
    simp [Complex.ratCast_re]
  -- Step 4: substitute hprod into hre, then cast to ℚ
  rw [hprod] at hre
  -- hre : (∏ σ, σ x).re = (Algebra.norm ℚ x : ℝ)
  -- hnneg : 0 ≤ (∏ σ, σ x).re
  -- hre ▸ hnneg : 0 ≤ (Algebra.norm ℚ x : ℝ)
  exact_mod_cast hre ▸ hnneg

end
