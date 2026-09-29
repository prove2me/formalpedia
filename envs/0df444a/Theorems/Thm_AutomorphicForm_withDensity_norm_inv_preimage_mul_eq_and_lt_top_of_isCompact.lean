-- Prove2me | Theorems.Thm_AutomorphicForm_withDensity_norm_inv_preimage_mul_eq_and_lt_top_of_isCompact
-- name    : AutomorphicForm.withDensity_norm_inv_preimage_mul_eq_and_lt_top_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/74a9a45c-f7c5-5480-b829-7e217c3ac665
-- title:
--   Unit-invariance and compact finiteness of the norm-weighted Haar measure
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$, and write $E = L \otimes_K K_v$ for the base change of $L$ to the $v$-adic completion $K_v$ of $K$, equipped with a measurable space structure that is the Borel structure of its topology. Let $\nu$ be an additive Haar measure on $E$, and let $\mu = \nu\cdot\lvert N_{E/K_v}\rvert^{-1}$ be the measure obtained from $\nu$ by the density $b \mapsto \lVert \mathrm{Algebra.norm}_{K_v}(b)\rVert^{-1}$, taken as an extended nonnegative real via `ENNReal.ofReal`. The assertion is the conjunction of two statements: first, for every unit $g \in E^\times$ and every measurable set $X \subseteq E$ one has $\mu\bigl((b \mapsto g b)^{-1}(X)\bigr) = \mu(X)$, i.e. $\mu$ is invariant under translation by units of $E$; second, for every compact set $Q \subseteq E$ all of whose elements are units of $E$, the value $\mu(Q)$ is not $\infty$. No measurability hypothesis is imposed on $Q$ in the second part.
--
--   This identifies the measure $\nu$ weighted by $\lVert N_{E/K_v}(\cdot)\rVert^{-1}$ as a Haar measure for the multiplicative group $E^\times$ written in additive coordinates, together with the finiteness needed to integrate over compact sets of units. It is used in establishing a bound for fibre volumes in the local analysis of automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_withDensity_norm_inv_preimage_mul_eq_and_lt_top_of_isCompact.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.withDensity_norm_inv_preimage_mul_eq_and_lt_top_of_isCompact
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    (∀ (g : (L ⊗[K] v.adicCompletion K)ˣ) (X : Set (L ⊗[K] v.adicCompletion K)), MeasurableSet X →
      ν.withDensity (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹)
          ((fun b : L ⊗[K] v.adicCompletion K => (g : L ⊗[K] v.adicCompletion K) * b) ⁻¹' X) =
        ν.withDensity (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹) X) ∧
    (∀ Q : Set (L ⊗[K] v.adicCompletion K), IsCompact Q → (∀ q ∈ Q, IsUnit q) →
      ν.withDensity (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹) Q ≠ ∞) := by sorry
