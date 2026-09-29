-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isLevelSphericalOfType_principal_flat_tendsto_rightConv_of_finiteDimensional
-- name    : AutomorphicForm.exists_isLevelSphericalOfType_principal_flat_tendsto_rightConv_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/651222a5-2e0c-544e-82d3-cfab6d517d50
-- title:
--   Spherical flat approximate identity at principal level
-- statement:
--   Let $F$ be a number field, $N \neq 0$ a nonzero ideal of $\mathcal O_F$, $\mathrm{tys}$ an archimedean type family on $F$ (for each infinite place $w$ a finite list of representations of the row-isometry subgroup of $\mathrm{GL}_2(F_w)$), and $\sigma$ a real number. Let $Y$ be a finite-dimensional $\mathbb C$-subspace of the space of functions $\mathrm{GL}_2(\mathbb A_F) \to \mathbb C$ all of whose members are continuous, are invariant under right translation by the compact group $U = K(N) \cap \ker(\mathrm{glArch})$, where $K(N)$ is `principalLevel`, the intersection of `levelOne` at $N$ with its conjugate by the Weyl element, and which lie in the cut submodule $\bigsqcap_w \bigsqcup_i$ of the type submodules attached to $\mathrm{tys}$. Then there is a sequence $f_n : \mathrm{GL}_2(\mathbb A_F) \to \mathbb C$ such that each $f_n$ is a factorizable test function (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor), is level-spherical of type $\mathrm{tys}$ for $U$ (an archimedean factor that is a test factor, bi-finite for $\mathrm{tys}$, and invariant under conjugation by row isometries at each infinite place, times the indicator of the image of $U$ in the finite component), and satisfies $\mathrm{flat}\,\sigma\,f_n = f_n$, i.e. $f_n(y) = \overline{f_n(y^{-1})}\,\|\det y\|^{-\sigma}$; and for every $y \in Y$ and every $g$, $(y * f_n)(g) = \int y(gx) f_n(x)\,dx \to y(g)$ as $n \to \infty$.
--
--   This is the approximate-identity statement for the full principal congruence level: the algebra of bi-$K$-finite, flat, level-spherical test functions acts on a finite-dimensional right-$U$-invariant space of the prescribed archimedean type with limits converging to the identity. It is used in the study of principal-level isotypic cusp spaces, notably for injectivity of right convolution on such spaces and for the construction of elements of the isotypic cuspidal submodule with prescribed convolution behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isLevelSphericalOfType_principal_flat_tendsto_rightConv_of_finiteDimensional.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isLevelSphericalOfType_principal_flat_tendsto_rightConv_of_finiteDimensional
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsFactorizableTestFn F (f n) ∧
        IsLevelSphericalOfType F tys (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (f n) ∧
        flat F σ (f n) = f n) ∧
      ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F,
        Filter.Tendsto (fun n => rightConv F y (f n) g) Filter.atTop (nhds (y g)) := by sorry
