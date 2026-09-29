-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_le_principal
-- name    : AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_le_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/3a4ba453-14f8-5b43-baa2-8325ee96084d
-- title:
--   A level-spherical test function injective on a finite-dimensional space
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, $N \neq 0$ an ideal of $\mathcal{O}_F$, $tys$ an archimedean type family for $F$ (a number $\mathrm{card}(w)$ of archimedean representation types $\mathrm{rep}(w,i)$ at each infinite place $w$), and $\sigma$ a real number. Let $Y$ be a finite-dimensional $\mathbb{C}$-submodule of the space of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ such that every $y \in Y$ is continuous; such that every $y \in Y$ is right invariant under the group attached to $N$ by the production pins built from $D$, the level map $N \mapsto K(N) \cap \ker(\mathrm{GL}_2(\mathbb{A}_F) \to \mathrm{GL}_2(\mathbb{A}_{F,\infty}))$ with $K(N)$ the principal level $\mathrm{levelOne}(N) \cap \mathrm{levelOne}(N)^{w}$ ($w$ the Weyl element), the Hecke generators $\mathrm{heckeGen}$ and the adelic box, i.e. $y(gu) = y(g)$ for all $g$ and all $u$ in that subgroup; and such that $Y$ is contained in $\mathrm{archCutSubmodule}\,tys$, the intersection over infinite places $w$ of the join of the archimedean type submodules $\mathrm{archTypeSubmoduleAt}(w,\mathrm{rep}(w,i))$, $i < \mathrm{card}(w)$. Then there is a function $f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ which is a factorizable test function (a product of a smooth compactly supported function of the archimedean matrix entries with a finite test factor evaluated on the finite part), which is level spherical of type $tys$ for that same subgroup $K(N) \cap \ker$ — that is, $f(g) = f_\infty(g_\infty)$ times the indicator of the image of the subgroup in $\mathrm{GL}_2(\mathbb{A}_{F,\mathrm{fin}})$ evaluated at $g_{\mathrm{fin}}$, with $f_\infty$ an archimedean test factor, bi-finite of type $tys$, and invariant under conjugation by the row-isometry subgroups at each infinite place — which satisfies $\overline{f(y^{-1})}\,\|\det y\|^{-\sigma} = f(y)$ for all $y$, and which is such that right convolution by $f$, $y \mapsto \big(g \mapsto \int y(gx) f(x)\,dx\big)$ against the adelic Haar measure, is injective on $Y$: if $y \in Y$ and $\mathrm{rightConv}\,y\,f = 0$ then $y = 0$.
--
--   This is the approximate-identity step in the study of isotypic spaces of automorphic forms: on a finite-dimensional space of continuous functions of fixed level and fixed archimedean types, some single smoothing operator of the prescribed shape is injective. It is the principal-level (full congruence subgroup) version, and it is used in the proofs that members of such spaces are right convolutions, and in the finite-dimensionality and $K$-finiteness statements for principal-level isotypic cusp spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_le_principal.lean

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

theorem AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_le_principal
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : Y ≤ levelInvariantSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      IsLevelSphericalOfType F tys ((productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f ∧
      flat F σ f = f ∧
      ∀ y ∈ Y, rightConv F y f = 0 → y = 0 := by sorry
