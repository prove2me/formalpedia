-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional
-- name    : AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/c4dcaf5c-5f6f-5b88-8f7f-5ab54e9fc0dc
-- title:
--   Flat level-spherical approximate identity for a finite-dimensional space
-- statement:
--   Let $F$ be a number field, $N \neq 0$ an ideal of $\mathcal{O}_F$, `tys` an archimedean type family for $F$ (a cardinality function $w \mapsto \mathrm{card}(w)$ on the infinite places together with, for each $w$, a finite list of finite-dimensional complex representations of the subgroup $\mathrm{rowIsometrySubgroup₀}$ of $\mathrm{GL}_2(F_w)$), and $\sigma \in \mathbb{R}$. Let $U$ denote `levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`, the intersection of the pullback along `glFin` of the finite level-one subgroup of level $N$ with the kernel of `glArch`, and let $Y$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ that is finite-dimensional, all of whose members are continuous and satisfy $y(gk) = y(g)$ for all $g$ and all $k \in U$, and which is contained in `archCutSubmodule F tys`, the infimum over the infinite places $w$ of the supremum over $i < \mathrm{card}(w)$ of the type submodules `archTypeSubmoduleAt F w (tys.rep w i)`. Then there is a sequence $f : \mathbb{N} \to (\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C})$ such that each $f_n$ is a factorizable test function (a product $f_n(g) = f_{n,\infty}(\mathrm{glArch}\,g) \cdot f_{n,\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_{n,\infty}$ of the form $\Phi \circ \mathrm{archEntries}$ for some $C^\infty$ function $\Phi$ on the matrix mixed space and of compact support, and $f_{n,\mathrm{fin}}$ locally constant of compact support); is level-$U$ spherical of type `tys`, i.e. $f_n(g) = f_{n,\infty}(\mathrm{glArch}\,g)$ times the indicator of the image of $U$ under `glFin` evaluated at $\mathrm{glFin}\,g$, where $f_{n,\infty}$ is an archimedean test factor satisfying `IsArchFactorBiFinite F tys` and is invariant under conjugation by $\mathrm{archRowIsometryInclAt₀}\,F\,w\,k$ for every infinite place $w$ and every $k$ in the row-isometry subgroup of $\mathrm{GL}_2(F_w)$; and is fixed by the $\sigma$-flat operation, $f_n(y) = \overline{f_n(y^{-1})} \cdot \|\det y\|_{\mathbb{A}}^{-\sigma}$; and such that for every $y \in Y$ and every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ the right convolutions $\int y(gx) f_n(x)\,dx$, taken against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, converge to $y(g)$ as $n \to \infty$.
--
--   This is an approximate-identity statement for the global Hecke algebra, with the extra feature that a single sequence of test functions, all of one fixed level, one fixed finite set of archimedean types and all fixed by the $\sigma$-flat involution, works simultaneously for every vector of the given finite-dimensional space $Y$. It is used to produce a smoothing operator in this class that is injective on a finite-dimensional cut of the cuspidal spectrum, in [`AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_le`](thm.html#AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsFactorizableTestFn F (f n) ∧
        IsLevelSphericalOfType F tys (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (f n) ∧
        flat F σ (f n) = f n) ∧
      ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F,
        Filter.Tendsto (fun n => rightConv F y (f n) g) Filter.atTop (nhds (y g)) := by sorry
