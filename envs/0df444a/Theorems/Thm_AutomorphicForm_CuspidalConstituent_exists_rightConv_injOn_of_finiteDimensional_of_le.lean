-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_le
-- name    : AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/c8b2a962-cbd8-5d49-87c9-cf71a705f40e
-- title:
--   Some level-spherical smoothing is injective on a finite-dimensional space
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, $N \neq 0$ an ideal of $\mathcal{O}_F$, $tys$ a family of archimedean types (for each infinite place $w$, a natural number $\mathrm{card}\,w$ and that many representations at $w$), and $\sigma$ a real number. Let $Y$ be a finite-dimensional $\mathbb{C}$-subspace of the functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, all of whose members are continuous, which is contained in the submodule of functions invariant under right translation by the subgroup $U =$ `levelOne` $(N) \sqcap$ `finiteAdelicGL2Subgroup` (finite component of level $N$, archimedean component trivial) and contained in `archCutSubmodule`, i.e. in $\bigsqcap_w \bigsqcup_{i}$ `archTypeSubmoduleAt` $(w, tys.\mathrm{rep}\,w\,i)$. Then there exists $f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ which is a factorizable test function (a product $f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ a compactly supported smooth function of the archimedean matrix entries and $f_{\mathrm{fin}}$ a finite test factor), which is level-spherical of type $tys$ for $U$ (so $f$ is $f_\infty \circ \mathrm{glArch}$ times the indicator of the image of $U$ under $\mathrm{glFin}$, with $f_\infty$ bi-finite of type $tys$ and invariant under conjugation by the row-isometry subgroups at all infinite places), satisfies $\overline{f(y^{-1})}\,\|\det y\|^{-\sigma} = f(y)$, and is such that right convolution against $f$, namely $g \mapsto \int y(gx) f(x)\,d\mu(x)$ for the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, is injective on $Y$: $y \in Y$ and $\mathrm{rightConv}(y, f) = 0$ force $y = 0$. The set $D$ enters only as a field of the carrier record whose level subgroup component is the prescribed $U$, so the hypotheses and conclusion do not depend on it.
--
--   This is the selection step of an approximate-identity argument: on a finite-dimensional space of continuous functions of prescribed level and archimedean types, one single smoothing operator from the level-spherical, flat-symmetric class already acts injectively. It is used downstream to produce functions in such a space as right convolutions, and thence in the identification of constituents with $K$-finite cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_le.lean

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

theorem AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_le
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : Y ≤ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      IsLevelSphericalOfType F tys ((productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f ∧
      flat F σ f = f ∧
      ∀ y ∈ Y, rightConv F y f = 0 → y = 0 := by sorry
