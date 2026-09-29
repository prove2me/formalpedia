-- Prove2me | Theorems.Thm_AutomorphicForm_mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul
-- name    : AutomorphicForm.mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/fe0c290e-21b1-5f6d-bd42-c8b48fbe5d65
-- title:
--   K-finiteness of smoothed isotypic cusp forms at principal level
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1$ and $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $W=\bigcup_{x\in T}\,\{g x : g\in \mathfrak{S}\}$ for the union of the right translates by elements of $T$ of the centre-cut Siegel set $\mathfrak{S}=\mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2$, consisting of those $g$ whose finite component is integral, with $c\le \mathrm{localHeight}$ of the archimedean component at every infinite place $w$, with $\mathrm{xWindowSq}$ of that component at most $u^2$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for every $w$. Assume $W$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\cdot z\in W$. Let $\mathrm{pins}$ be the production pins attached to $W$ with Borel structure and Haar measure of $\mathrm{GL}_2(\mathbb{A}_F)$, central subgroup $\top$, level family $N\mapsto \mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $v\mapsto \mathrm{heckeGen}\,v$, and the additive adelic Haar measure conditioned on $\mathrm{adelicBox}\,F$; let $\xi$ be a homomorphism from its central subgroup to $\mathbb{C}^\times$. Let $N$ be an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, $\Psi$ a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with families $a_v,b_v$), and $\mathrm{tys}$ a family of archimedean types, i.e. for each infinite place $w$ a finite list $\mathrm{rep}\,w\,i$ of archimedean representations. Let $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be factorizable, $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ an archimedean and $f_{\mathrm{fin}}$ a finite test factor, let $\lambda\neq 0$, and let $\varphi$ lie in the intersection of the $\mathbb{C}$-span of the isotypic cusp forms $\mathrm{IsIsotypicCuspFormAt}\,F\,\mathrm{pins}\,\xi\,N\,S\,\Psi$ with $\bigsqcap_w\bigsqcup_i \mathrm{archTypeSubmoduleAt}\,F\,w\,(\mathrm{tys.rep}\,w\,i)$, and satisfy $\mathrm{rightConv}\,F\,\varphi\,f=\lambda\varphi$, where $(\mathrm{rightConv}\,F\,\varphi\,f)(g)=\int \varphi(gx)f(x)\,d\mu(x)$ for adelic Haar measure $\mu$. Then $\varphi$ belongs to $\mathrm{cuspKFiniteSubmodule}\,F\,\mathrm{pins}\,\xi$, the $\mathbb{C}$-span of those functions that are continuous, all of whose right translates are smooth cuspidal automorphic at the pins with central character $\xi$, and which lie in the archimedean cut submodule of some family of archimedean types.
--
--   This is the principal-congruence-level form of the passage from an isotypic Hecke eigenspace, cut by archimedean types and smoothed by a factorizable test function with nonzero eigenvalue, into the $K$-finite smooth cuspidal space attached to the production pins. It feeds the principal-level constituent dictionary [`AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul`](thm.html#AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_NumberField_PrincipalLevel

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

theorem AutomorphicForm.mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (lam : ℂ) (hlam : lam ≠ 0)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys)
    (heig : rightConv F φ f = lam • φ) :
    φ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by sorry
