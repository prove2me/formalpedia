-- Prove2me | Theorems.Thm_DedekindZeta_Theta_traceForm_mixedEmbedding_int_iff_mem_dualIdeal
-- name    : DedekindZeta.Theta.traceForm_mixedEmbedding_int_iff_mem_dualIdeal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:11:08.600123+00:00
-- url     : https://prove2.me/theorems/c6644ecd-fda7-4fb4-af8b-e2a4c1c34f03
-- title:
--   Theta: trace Form mixed Embedding int iff mem dual Ideal
-- statement:
--   **Trace-dual identification, `K`-rational form** (the standard treatment).
--   A field element `b : K` pairs integrally under
--   the symmetric trace form `T` with every element of the ideal `𝔞` iff `b` lies in
--   the dual ideal `(𝔞𝔡)⁻¹ = dualIdeal K 𝔞`. This is the element-level core of the
--   trace-dual statement: `traceForm_mixedEmbedding`
--   (`T(mixedEmbedding b, a) = (algebraMap ℚ ℝ)(Tr_{K/ℚ}(b·a))`) turns the integrality
--   into `Tr(b·a) ∈ ℤ`, which by `FractionalIdeal.mem_dual` and `dualIdeal_eq_dual` is
--   exactly membership of `b` in `dualIdeal K 𝔞`. NB: this is the *symmetric* trace
--   form, with no complex conjugation — the conjugation twist lives in the passage
--   from the Hermitian Minkowski inner product to `T` (`dual_idealLattice`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L570-L588
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L570-L588

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.traceForm_mixedEmbedding_int_iff_mem_dualIdeal
    (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (b : K) :
    (∀ a ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∃ k : ℤ,
        traceForm K (mixedEmbedding K b) a = (k : ℝ)) ↔
      b ∈ (dualIdeal K 𝔞 : Submodule (𝓞 K) K) := by sorry
