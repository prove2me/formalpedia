-- Prove2me | solution 1 for flt5_ck5_prod_normSq_pair_exists
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:59:44.230729+00:00
-- url     : https://prove2.me/submissions/823b6a83-0ca2-4116-847c-7edd41190666
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Norm.Transitivity
import Theorems.Thm_flt5_ck5_conj_pair_prod

-- Sketch: flt5_ck5_prod_normSq_pair_exists
-- CK5 is totally imaginary, so its 4 complex embeddings split into 2 conjugate pairs.
-- Child flt5_ck5_conj_pair_prod gives σ₁, σ₂ such that ∀ x,
--   ∏ σ, σ x = ↑(normSq σ₁ x * normSq σ₂ x).
-- This is the key fact that CK5 has degree 4 over ℚ with no real embeddings.

noncomputable section

abbrev CK5ps := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5ps :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5ps :=
  IsCyclotomicExtension.numberField {5} ℚ CK5ps

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

instance : IsGalois ℚ CK5ps :=
  IsCyclotomicExtension.isGalois {5} ℚ CK5ps

theorem solution :
    ∃ (σ₁ σ₂ : CK5ps →ₐ[ℚ] ℂ),
    ∀ (x : CK5ps),
    (∏ σ : CK5ps →ₐ[ℚ] ℂ, σ x) = ↑(Complex.normSq (σ₁ x) * Complex.normSq (σ₂ x)) :=
  flt5_ck5_conj_pair_prod

end
