-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule
-- name    : AutomorphicForm.CuspidalConstituent.rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/abc8c03c-0472-5876-a031-c55e11ca789d
-- title:
--   Smoothing preserves the isotypic cuspidal archimedean cut
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1$ and $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}(\,\cdot\,x)(\Sigma)$ for the union of the right translates by elements of $T$ of the centre-cut Siegel set $\Sigma$ of those $g$ whose finite part lies in the integral subgroup $\mathrm{finiteIntegralGL2}$ and whose component at each infinite place $w$ satisfies $\mathrm{localHeight}\ge c$, $\mathrm{xWindowSq}\le u^2$ and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$. Assume $D$ covers modulo centre: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an adelic unit $z$ with $\gamma g\cdot z\in D$. Let `pins` be `productionPinsOf` for the data $D$, the level groups $N\mapsto \mathrm{levelOne}(N)\sqcap \ker(\mathrm{glArch})$, the Hecke generators $v\mapsto \mathrm{heckeGen}(v)$ and the box `adelicBox` — so the measure is the Borel Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the centre subgroup is $\top$, and the additive measure is adelic Haar measure conditioned on `adelicBox`. Let $\xi:\top\to\mathbb{C}^\times$ be a character, $N\ne 0$ an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, `tys` an archimedean type family, and $\Psi$ a complex Hecke eigensystem. Let $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a factorizable test function (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor) which is archimedean bi-finite for `tys` (that is, $x\mapsto f(x^{-1})$ lies in `archCutSubmodule` and $f$ in `archDualCutSubmodule`) and whose support satisfies: every $x$ with $f(x)\ne 0$ factors as $x=ak$ with $\mathrm{glFin}(a)=1$ and $k\in \mathrm{levelOne}(N)\sqcap\ker(\mathrm{glArch})$. Then for every $\varphi$ in the intersection of `isotypicCuspSubmodule` for these `pins`, $\xi$, $N$, $S$, $\Psi$ — the $\mathbb{C}$-span of the continuous smooth cusp automorphic functions that are right invariant under the level group at $N$, are Hecke coset eigenfunctions with eigenvalue $\Psi.a(v)$ for $v\notin S$, and satisfy the central eigenvalue relation with $\Psi$'s central character values off $S$ — with `archCutSubmodule` for `tys` (the intersection over infinite places of the sums of the type submodules attached to the representations $\mathrm{tys.rep}\,w\,i$), the right convolution $g\mapsto\int \varphi(gx)f(x)\,d\mu(x)$ again lies in that same intersection.
--
--   This is the stability of the isotypic cuspidal cut under smoothing by a test function concentrated in $\mathrm{GL}_2(F_\infty)\cdot U(N)$: convolution on the right preserves cuspidality, level invariance, the Hecke and central eigenvalues off $S$, and the prescribed archimedean types. It is used where polynomials in the smoothing operator must be kept inside the isotypic cut, notably in the decomposition of isotypic cusp forms as sums of right convolutions and in the class-sum growth estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule.lean

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

theorem AutomorphicForm.CuspidalConstituent.rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N ∧ x = a * k)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys) :
    rightConv F φ f ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys := by sorry
