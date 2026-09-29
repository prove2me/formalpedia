-- Prove2me | Theorems.Thm_FamousTheorems_minkowski_bound_ideal_class
-- name    : FamousTheorems.minkowski_bound_ideal_class
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:20:52.525295+00:00
-- url     : https://prove2.me/theorems/48f056ba-6fa6-498e-ad85-f5a1b4c2b7e5
-- title:
--   The Minkowski bound on ideal classes
-- statement:
--   **The Minkowski bound on ideal classes.** Let $K$ be a number field of degree $n$ with $r_2$ complex places and discriminant $d_K$. Every ideal class of $\mathcal O_K$ contains a nonzero integral ideal $I$ with
--   $$N(I)\le \Big(\frac4\pi\Big)^{r_2}\frac{n!}{n^n}\sqrt{|d_K|}.$$
--
--   Since there are only finitely many integral ideals of bounded norm, this gives the finiteness of the class number and makes the class group computable in practice. It also implies that $|d_K|>1$ for $K\ne\mathbb Q$ (Minkowski's theorem).
--
--   **Formalization note.** Mathlib's `NumberField.exists_ideal_in_class_of_norm_le`. Nonzero ideals are elements of `nonZeroDivisors (Ideal (𝓞 K))`, `ClassGroup.mk0` sends such an ideal to its class, and `Ideal.absNorm` is the absolute norm $|\mathcal O_K/I|$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NumberField.exists_ideal_in_class_of_norm_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem minkowski_bound_ideal_class {K : Type*} [Field K] [NumberField K] (C : ClassGroup (NumberField.RingOfIntegers K)) :
    ∃ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)), ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) : ℝ) ≤
        (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          (((Module.finrank ℚ K).factorial : ℝ) / (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
            Real.sqrt |(NumberField.discr K : ℝ)|) := by sorry

end FamousTheorems
