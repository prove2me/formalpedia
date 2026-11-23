-- Prove2me | Theorems.Thm_DedekindZeta_Theta_dual_idealLattice
-- name    : DedekindZeta.Theta.dual_idealLattice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:13:24.199799+00:00
-- url     : https://prove2.me/theorems/1718940d-c035-4018-a211-ea957f29a7a2
-- title:
--   Theta: dual ideal Lattice
-- statement:
--   **Duality of the lattices, Hermitian Minkowski dual** (the standard treatment corrected for the complex-conjugation twist). With respect to the
--   Minkowski inner product (which is the
--   *Hermitian* form `Re ∑_σ conj(σx)·σy`, see `inner_eEmbℝ_eq_traceForm_conjMixed`),
--   a point `y : K_ℝ` lies in the dual lattice of `Λ(𝔞)` (its inner product with
--   every point of `Λ(𝔞)` is an integer) iff its conjugate `conjMink K y` lies in
--   `Λ((𝔞𝔡)⁻¹)`. The naive (untwisted) form `y ∈ Λ((𝔞𝔡)⁻¹)` is **false for
--   non-CM `K`** (e.g. `K = ℚ(∛2)`): the symmetric trace-form duality identifies the
--   trace-dual with `Λ((𝔞𝔡)⁻¹)`, but the Hermitian inner product introduces the
--   conjugation `conjMink`, which preserves `Λ((𝔞𝔡)⁻¹)` setwise only in the CM /
--   totally-real case. Since `conjMink` is an involution this is equivalent to
--   `y ∈ conjMink '' Λ((𝔞𝔡)⁻¹)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L788-L806
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L788-L806

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.dual_idealLattice (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0)
    (y : minkowskiSpace K) :
    (∀ x ∈ idealLattice K (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∃ k : ℤ,
        (inner ℝ y x : ℝ) = k) ↔
      conjMink K y ∈ idealLattice K (dualIdeal K 𝔞) := by sorry
