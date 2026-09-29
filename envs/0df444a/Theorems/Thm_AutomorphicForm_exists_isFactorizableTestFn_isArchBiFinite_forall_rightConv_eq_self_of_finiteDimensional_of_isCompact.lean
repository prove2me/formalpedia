-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_forall_rightConv_eq_self_of_finiteDimensional_of_isCompact
-- name    : AutomorphicForm.exists_isFactorizableTestFn_isArchBiFinite_forall_rightConv_eq_self_of_finiteDimensional_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/08d3f13a-d104-5f5d-ad6d-63cc9806f103
-- title:
--   One bi-finite test function reproduces a finite-dimensional cut
-- statement:
--   Let $F$ be a number field and write $G=\mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`. Let $U\le G$ be a subgroup whose underlying set is compact, $O\le G$ a subgroup whose underlying set is open, with $U=O\cap\ker(\mathrm{glArch})$, the second factor being the subgroup of elements with trivial archimedean component. Let `tys` be an archimedean type family: for each infinite place $w$ a finite list of pairs consisting of a natural number $n$ and a representation of $\mathrm{rowIsometrySubgroup}_0$ of $F_w$ on $\mathbb{C}^n$. Let $Y\subseteq(G\to\mathbb{C})$ be a $\mathbb{C}$-submodule that is finite-dimensional, all of whose members are continuous and satisfy $y(gk)=y(g)$ for $g\in G$, $k\in U$, with $Y$ contained in the archimedean cut $\bigsqcap_w\bigvee_i$ of the type submodules attached to `tys`, and stable under right convolution by every factorizable test function that is level-spherical of type $(\mathrm{tys},U)$. Then there is a single function $f:G\to\mathbb{C}$ which is a factorizable test function (product of a compactly supported smooth archimedean factor in the matrix entries and a compactly supported locally constant finite factor), is level-spherical of type $(\mathrm{tys},U)$, i.e. $f(g)=f_\infty(g_\infty)\mathbf 1_{U}(g_{\mathrm{fin}})$ with $f_\infty$ an archimedean test factor, bi-finite for `tys` and invariant under conjugation by row isometries at each infinite place, satisfies `IsArchBiFinite F tys f` (that is, $x\mapsto f(x^{-1})$ lies in the archimedean cut and $f$ in the dual cut for `tys`), and reproduces $Y$ exactly: $\int_G y(gx)f(x)\,dx=y(g)$ for all $y\in Y$ and all $g$, the integral being taken against the adelic Haar measure on $G$.
--
--   This is the reproduction, or exact approximate identity, step: on a finite-dimensional space of continuous, right-$U$-invariant functions of fixed archimedean type which is stable under the relevant Hecke algebra, one factorizable level-spherical and archimedean bi-finite test function acts as the identity operator. It is obtained from the corresponding convergence statement, in which a sequence of such test functions is produced with $y*f_n\to y$ pointwise, and it feeds the construction of test functions reproducing a given vector of the level-invariant part of the archimedean cut in the cuspidal constituent development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_forall_rightConv_eq_self_of_finiteDimensional_of_isCompact.lean

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

theorem AutomorphicForm.exists_isFactorizableTestFn_isArchBiFinite_forall_rightConv_eq_self_of_finiteDimensional_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys)
    (hYs : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsLevelSphericalOfType F tys U f →
      ∀ y ∈ Y, rightConv F y f ∈ Y) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ,
      IsFactorizableTestFn F f ∧ IsLevelSphericalOfType F tys U f ∧ IsArchBiFinite F tys f ∧
        ∀ y ∈ Y, rightConv F y f = y := by sorry
