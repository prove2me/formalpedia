-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
-- name    : AutomorphicForm.CuspidalConstituent.rightConv_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/8c02b8c5-4d9c-556a-a27a-854547ea5736
-- title:
--   Right convolution preserves the isotypic cuspidal cut at principal level
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1$ and $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}(\,\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\;F\;c\;u\;d_1\;d_2\,]$, the union of the right translates by the elements of $T$ of the set of $g$ whose finite part lies in $\mathrm{GL}_2(\widehat{\mathcal O_F})$, whose archimedean component satisfies $c\le\mathrm{localHeight}$ and $\mathrm{xWindowSq}\le u^2$ at every infinite place, and whose archimedean determinant norm lies in $[d_1,d_2]$ at every infinite place; assume `CoversModCentre`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ can be written $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(F)$ and some central adelic scalar $z$. Let `pins` be the carrier data `productionPinsOf` attached to $D$, to the level family $N\mapsto \mathrm{principalLevel}(N)\sqcap \mathrm{finiteAdelicGL2Subgroup}$, to the Hecke generators $v\mapsto \mathrm{heckeGen}\,v$ and to the box `adelicBox F`; so its measure is adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, its central subgroup $Z$ is all of $(\mathbb{A}_F)^\times$, and its additive measure is adelic Haar conditioned on the box. Let $\xi:Z\to\mathbb{C}^\times$ be a character, $N\ne 0$ an ideal of $\mathcal O_F$, $S$ a finite set of finite places, `tys` a family assigning to each infinite place $w$ finitely many representations of $\mathrm{rowIsometrySubgroup}_0(F_w)$, and $\Psi$ a Hecke eigensystem over $\mathbb{C}$. Let $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be factorizable, that is a product of a compactly supported archimedean factor which is a smooth function of the matrix entries with a locally constant compactly supported finite factor; assume $f$ is bi-finite for `tys`, i.e. $x\mapsto f(x^{-1})$ lies in $\mathrm{archCutSubmodule}\;F\;\mathrm{tys}$ and $f$ lies in $\mathrm{archDualCutSubmodule}\;F\;\mathrm{tys}$, and assume every $x$ with $f(x)\ne 0$ factors as $x=ak$ with $\mathrm{glFin}(a)=1$ and $k\in \mathrm{principalLevel}(N)\sqcap \mathrm{finiteAdelicGL2Subgroup}$. Then for every $\varphi$ in the intersection of $\mathrm{isotypicCuspSubmodule}\;F\;\mathrm{pins}\;\xi\;N\;S\;\Psi$ — the $\mathbb{C}$-span of the continuous smooth cuspidal automorphic functions with central character $\xi$ that are right invariant under $\mathrm{pins}.U\,N$ and, at every $v\notin S$, are Hecke coset eigenfunctions with eigenvalue $\Psi.a\,v$ and satisfy $\varphi(\mathrm{scalar}(\det \mathrm{heckeGen}\,v)\,g)=\Psi.b\,v\cdot\varphi(g)$ — with $\mathrm{archCutSubmodule}\;F\;\mathrm{tys}=\bigsqcap_w\bigsqcup_i \mathrm{archTypeSubmoduleAt}\;F\;w\;(\mathrm{tys.rep}\;w\;i)$, the right convolution $g\mapsto\int \varphi(gx)f(x)\,d\mu(x)$ again lies in that same intersection.
--
--   This is the stability of an isotypic cuspidal eigenspace under smoothing by a test function whose support is contained in $\mathrm{GL}_2(F_\infty)\cdot U(N)$, here for the principal congruence level family $N\mapsto \mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$. It is used by the finite spectral expansion [`AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule`](thm.html#AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule), where polynomials in the smoothing operator must remain inside the isotypic cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule.lean

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

theorem AutomorphicForm.CuspidalConstituent.rightConv_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N ∧ x = a * k)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys) :
    rightConv F φ f ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys := by sorry
