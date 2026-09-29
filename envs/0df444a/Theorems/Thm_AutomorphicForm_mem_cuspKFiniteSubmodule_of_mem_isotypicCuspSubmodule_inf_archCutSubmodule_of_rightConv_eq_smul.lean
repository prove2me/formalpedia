-- Prove2me | Theorems.Thm_AutomorphicForm_mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
-- name    : AutomorphicForm.mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/3561b6e3-555c-54ef-9f12-5ca18a020481
-- title:
--   Convolution eigenvectors of isotypic cusp forms are K-finite
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $W=\bigcup_{x\in T}\{gx : g\in \mathfrak S\}$ for the union of the right translates by elements of $T$ of the centre-cut Siegel set $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂`, consisting of those $g$ whose finite component lies in the integral subgroup, whose archimedean components have local height at least $c$ and $x$-window square at most $u^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_1,d_2]$ at every infinite place; assume $W$ covers modulo the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g z\in W$. Let `pins` be the carrier data `productionPinsOf` attached to $W$, to the levels $N\mapsto$ `levelOne` $\cap\ \ker(\mathrm{glArch})$, to the Hecke generators `heckeGen`, and to the adelic box, so that its central subgroup is all of $(\mathbb{A}_F)^\times$, its measures are the adelic $\mathrm{GL}_2$ Haar measure and the additive adelic Haar measure conditioned on the box; let $\xi$ be a homomorphism from that central subgroup to $\mathbb{C}^\times$. Let $N$ be an ideal of $\mathcal O_F$, $S$ a finite set of finite places, $\Psi$ a Hecke eigensystem over $\mathbb{C}$ (a level ideal $\neq\bot$ together with families $a,b$ of complex coefficients indexed by the finite places), and `tys` an archimedean type family, assigning to each infinite place $w$ a natural number and that many archimedean representation types at $w$. Let $f$ be factorizable, that is $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for an archimedean and a finite test factor, and let $\lambda\neq 0$. Suppose $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ lies both in the span of the functions satisfying the isotypic cusp form predicate `IsIsotypicCuspFormAt` for the data $(\xi,N,S,\Psi)$ at these pins and in the archimedean cut submodule $\bigsqcap_w\bigvee_i$ `archTypeSubmoduleAt` determined by `tys`, and that $\varphi$ is an eigenvector of right convolution by $f$, namely $g\mapsto\int \varphi(gx)f(x)\,d\mu(x)$ equals $\lambda\varphi$. Then $\varphi$ lies in `cuspKFiniteSubmodule` for these pins and $\xi$: the span of those continuous functions all of whose right translates satisfy `IsSmoothCuspAutomorphicFnAt` at the pins with character $\xi$ and which lie in the archimedean cut submodule of some archimedean type family.
--
--   This is the step passing from an abstract isotypic cuspidal eigenvector of a smoothing operator to an element of the $K$-finite smooth cuspidal space, the boundedness of convolutions of cusp forms on Siegel sets in the style of Godement's spectral decomposition. It feeds the decomposition of isotypic cuspidal spaces into cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

open AutomorphicForm.CuspidalSpectrum
open scoped ENNReal

theorem AutomorphicForm.mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (lam : ℂ) (hlam : lam ≠ 0)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys)
    (heig : rightConv F φ f = lam • φ) :
    φ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by sorry
