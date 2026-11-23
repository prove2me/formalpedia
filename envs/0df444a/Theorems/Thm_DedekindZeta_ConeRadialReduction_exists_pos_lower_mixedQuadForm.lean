-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_pos_lower_mixedQuadForm
-- name    : DedekindZeta.ConeRadialReduction.exists_pos_lower_mixedQuadForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:49:11.572971+00:00
-- url     : https://prove2.me/theorems/c2ebd0ec-48a4-4628-9ca3-528386db75ac
-- title:
--   Cone Radial Reduction: exists pos lower mixed Quad Form
-- statement:
--   **Uniform positive lower bound on the nonzero Minkowski norms over the
--   surface.** There is `q > 0` with `q ≤ Q(σ · σ(a))` for every `σ` on the norm-1
--   surface fundamental domain and every nonzero `a ∈ 𝔞`. The points `σ · σ(a)`
--   range over a (rescaled) lattice with no accumulation at `0` away from `a = 0`,
--   and the surface is relatively compact, so the smallest nonzero squared norm is
--   bounded below by a positive constant. the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1302-L1424
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1302-L1424

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem DedekindZeta.ConeRadialReduction.exists_pos_lower_mixedQuadForm (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ q : ℝ, 0 < q ∧ ∀ σ ∈ normEqOneSurface K,
      ∀ a : 𝓞 K, a ∈ 𝔞 → a ≠ 0 →
        q ≤ mixedQuadForm K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) := by sorry
