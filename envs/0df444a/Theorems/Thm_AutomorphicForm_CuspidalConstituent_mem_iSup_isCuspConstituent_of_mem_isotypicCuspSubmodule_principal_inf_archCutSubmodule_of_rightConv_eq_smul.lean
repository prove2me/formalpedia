-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul
-- name    : AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/dd272232-cb6f-5554-bfaf-d2f644835173
-- title:
--   Isotypic cusp eigenfunctions lie in a sum of cuspidal constituents
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adele ring of $F$. Write $W=\bigcup_{x\in T}\,\mathfrak S\,x$ for the union of the right translates by $T$ of the centre-cut Siegel set $\mathfrak S$ of parameters $c,u,d_1,d_2$, whose members are those $g$ whose finite part is finite-integral, with $c\le$ the local height of the archimedean component at every infinite place, with archimedean window square $\le u^2$, and with archimedean determinant norm in $[d_1,d_2]$ at every infinite place; it is assumed that $W$ covers modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g z\in W$. Let `pins` be the carrier pins built from $W$ by `productionPinsOf`: Borel structure and Haar measure of adelic $\mathrm{GL}_2$, domain $W$, central subgroup the whole idele class group of units, level family $N\mapsto \mathrm{principalLevel}\sqcap$ the finite-adelic subgroup (the kernel of the archimedean projection), Hecke generators `heckeGen` at the finite places, and the Haar measure on the adeles conditioned on `adelicBox`. Let $\xi$ be a homomorphism from the central subgroup of `pins` to $\mathbb C^\times$, let $N$ be a nonzero ideal of $\mathcal O_F$, $S$ a finite set of finite places, `tys` an archimedean type family (a finite list of archimedean types at each infinite place) and $\Psi$ a Hecke eigensystem over $\mathbb C$. Let $f$ be a factorizable test function, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean test factor and a finite test factor, let $\lambda\neq0$, and let $\varphi$ lie in the intersection of the isotypic cusp submodule $\mathrm{span}_{\mathbb C}\{\psi\mid \mathrm{IsIsotypicCuspFormAt}\ \text{for}\ \mathrm{pins},\xi,N,S,\Psi\}$ with the archimedean cut submodule $\bigsqcap_w\bigsqcup_{i<\mathrm{card}(w)}$ of the type submodules of `tys`, and satisfy $\mathrm{rightConv}(\varphi,f)=\lambda\varphi$, where $\mathrm{rightConv}(\varphi,f)(g)=\int\varphi(gx)f(x)\,d\mu(x)$ for adelic $\mathrm{GL}_2$ Haar measure $\mu$. Then $\varphi$ lies in the supremum, over complex submodules $V$ of functions on adelic $\mathrm{GL}_2$, of those $V$ that are cuspidal constituents for `pins` and $\xi$ (a cusp subrepresentation, nonzero, with every cusp subrepresentation contained in it equal to $\bot$ or to $V$), that contain some nonzero function which is an isotypic cusp form at `pins`, $\xi$, $N$, $S$, $\Psi$, and whose intersection with the archimedean cut submodule is nonzero.
--
--   This is the principal-congruence form of the discrete decomposition of the cuspidal spectrum of $\mathrm{GL}_2$ in the isotypic picture: an eigenfunction of a smoothing operator with nonzero eigenvalue, lying in the isotypic cusp space of a fixed level, Hecke datum and archimedean type family, is captured by the cuspidal constituents that meet that datum and that type family. It feeds the finite spectral expansion of such an eigenfunction and the inclusion of the isotypic cusp space cut by archimedean types into the supremum of constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (lam : ℂ) (hlam : lam ≠ 0)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys)
    (heig : rightConv F φ f = lam • φ) :
    φ ∈ ⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V ∧ CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ V ∧
              V ⊓ archCutSubmodule F tys ≠ ⊥), V := by sorry
