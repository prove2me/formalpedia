-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_rightConv_eq_smul
-- name    : AutomorphicForm.CuspidalSpectrum.mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_rightConv_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/0922214c-7a9d-54db-a337-af83309697eb
-- title:
--   Convolution eigenfunctions among cuspidal members are K-finite
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $F$; write $W=\bigcup_{x\in T}\,\{s x: s\in \mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in the integral subgroup, whose archimedean components at every infinite place have local height at least $c$, window coordinate $\le u^2$, and determinant norm in $[d_1,d_2]$. Assume $W$ covers modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\cdot z I\in W$. Let $\xi$ be a homomorphism from the full group of idele units to $\mathbb C^\times$, let $\alpha,\beta$ be reals and $\Phi_0$ a slab fundamental domain for these: $0<\alpha<\beta$, $\Phi_0$ is contained in the set where the idele norm of the determinant lies in $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on that slab with the restricted adelic Haar measure. Let `tys` be an archimedean type family, and let $f$ be a factorizable test function (a product of a compactly supported function of the archimedean matrix entries which is smooth in those entries with a compactly supported locally constant function of the finite part) which is archimedean bi-finite of type `tys`, meaning $g\mapsto f(g^{-1})$ lies in the archimedean cut submodule and $f$ in the archimedean dual cut submodule for `tys`. Let $\lambda\neq 0$ and let $\psi$ be a continuous function lying in `cuspMemberSubmodule F Φ₀ ξ`, i.e. continuous and smooth cuspidal automorphic at the pins attached to $\Phi_0$ with central character $\xi$, and suppose the right convolution `rightConv F ψ f` equals $\lambda\psi$. Then $\psi$ belongs to `cuspKFiniteSubmodule` for the character $\xi$ and for the pins `productionPinsOf` built from the domain $W$, the level subgroups $N\mapsto$ `levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`, the Hecke generators `heckeGen (𝓞 F) F v`, and the adelic additive Haar measure conditioned on the box `adelicBox F`; that is, $\psi$ lies in the span of those $\varphi$ all of whose right translates are smooth cuspidal automorphic at these pins, which are continuous and lie in the archimedean cut submodule of some type family.
--
--   This is the standard passage from an abstract cuspidal $L^2$-member on a slab fundamental domain to a $K$-finite smooth cuspidal vector over a Siegel-window carrier, the convolution eigenfunction equation supplying the archimedean type and the integrability on the window. It feeds the decomposition of isotypic cusp spaces into cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_rightConv_eq_smul.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_rightConv_eq_smul
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f)
    (lam : ℂ) (hlam : lam ≠ 0)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ cuspMemberSubmodule F Φ₀ ξ) (heig : rightConv F ψ f = lam • ψ) :
    ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by sorry
