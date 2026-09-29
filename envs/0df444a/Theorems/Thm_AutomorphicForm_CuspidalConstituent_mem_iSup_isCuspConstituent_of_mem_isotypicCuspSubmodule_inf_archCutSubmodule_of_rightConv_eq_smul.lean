-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
-- name    : AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/53bc3d8f-89f0-5b24-ac3d-1f2f3aa5f224
-- title:
--   Non-zero eigenvectors of the isotypic type-cut lie in the cuspidal constituents
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2$ of the adele ring of $F$. Write $\mathfrak S=\bigcup_{x\in T}\{g x: g\in \mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\}$, the union of right translates by $T$ of the set of $g$ whose finite part is integral, whose archimedean components have local height at least $c$ and window square at most $u^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_1,d_2]$ at every infinite place; assume `CoversModCentre F` holds for $\mathfrak S$, i.e. every $g$ can be moved into $\mathfrak S$ by left multiplication by a global point of $\mathrm{GL}_2(F)$ and right multiplication by a central adelic scalar. All notions are taken at the pins `productionPinsOf` over the window $\mathfrak S$, with Borel structure and Haar measure of $\mathrm{GL}_2$ of the adeles, level subgroups $N\mapsto \mathrm{levelOne}\,N\sqcap$ the kernel of the archimedean projection, Hecke generators $\mathrm{heckeGen}$ at the finite places, and the additive measure conditioned on `adelicBox`; for these pins the central subgroup is all of $(\mathbb A_F)^\times$, and $\xi$ is a character of it with values in $\mathbb C^\times$. Let $N$ be a non-zero ideal of $\mathcal O_F$, $S$ a finite set of finite places, $\mathrm{tys}$ an archimedean type family (a finite list of archimedean representation types at each infinite place), $\Psi$ a Hecke eigensystem over $\mathbb C$ (a non-zero level together with eigenvalue data $a_v,b_v$), $f$ a factorizable test function (a product of an archimedean and a finite test factor), and $\lambda\neq 0$. Let $\varphi$ lie in the intersection of the span of the isotypic cusp forms at these pins for $(\xi,N,S,\Psi)$ with the archimedean cut submodule $\bigsqcap_w\bigsqcup_i$ of the type submodules attached to $\mathrm{tys}$, and suppose the right convolution $g\mapsto\int \varphi(gx)f(x)\,d\mu(x)$ equals $\lambda\varphi$. Then $\varphi$ belongs to the supremum of those submodules $V$ of $\mathbb C$-valued functions on $\mathrm{GL}_2$ of the adeles which are cuspidal constituents for these pins and $\xi$ (a non-zero cusp subrepresentation all of whose cusp subrepresentations contained in it are $0$ or $V$), which meet the datum $(N,S,\Psi)$ in the sense that $V$ contains a non-zero isotypic cusp form for it, and which satisfy $V\sqcap\mathrm{archCutSubmodule}\,F\,\mathrm{tys}\neq\bot$. No positivity is assumed on $c$, $u$, $d_1$ or $d_2$ beyond $d_1<d_2$.
--
--   This is the spectral decomposition step for the cuspidal spectrum of $\mathrm{GL}_2$ over a number field in the form needed here: a convolution eigenvector with non-zero eigenvalue inside an isotypic and archimedean-type cut is exhausted by the irreducible cuspidal constituents that see the same Hecke datum and the same archimedean types. It is used to prove that the whole isotypic type-cut is contained in the sum of such constituents, to write eigenvectors as finite sums of constituent members, and in the class-sum growth estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (lam : ℂ) (hlam : lam ≠ 0)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys)
    (heig : rightConv F φ f = lam • φ) :
    φ ∈ ⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V ∧ CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ V ∧
              V ⊓ archCutSubmodule F tys ≠ ⊥), V := by sorry
