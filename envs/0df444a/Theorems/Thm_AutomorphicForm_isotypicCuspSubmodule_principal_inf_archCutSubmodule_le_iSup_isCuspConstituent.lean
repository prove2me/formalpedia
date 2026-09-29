-- Prove2me | Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_principal_inf_archCutSubmodule_le_iSup_isCuspConstituent
-- name    : AutomorphicForm.isotypicCuspSubmodule_principal_inf_archCutSubmodule_le_iSup_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/a4b6e393-9f3b-53a6-bd9e-bcb0e35fe7e6
-- title:
--   Principal-level isotypic cusp forms lie in sum of cuspidal constituents
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\mathfrak{S}x$, the union of the right translates by the elements of $T$ of the centre-cut Siegel set $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` (finite part integral, all archimedean local heights $\ge c$, all archimedean $x$-windows bounded by $u^2$, all archimedean determinant norms in $[d_1,d_2]$), and assume `CoversModCentre F D`: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in D$. Let `pins` be the production pins on $D$ with level family $N\mapsto$ `principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`, Hecke generators `heckeGen` and the adelic box, so that the central subgroup is all of $(\mathbb{A}_F)^\times$, and let $\xi$ be a character of it. Let $N$ be an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, `tys` an archimedean type family and $\Psi$ a Hecke eigensystem over $\mathbb{C}$. Then the intersection of `isotypicCuspSubmodule F pins ξ N S Ψ` (the $\mathbb{C}$-span of the forms $\varphi$ with `IsIsotypicCuspFormAt F pins ξ N S Ψ φ`) with `archCutSubmodule F tys` $=\bigsqcap_w\bigsqcup_i$ `archTypeSubmoduleAt F w (tys.rep w i)` is contained in the supremum of those submodules $V$ of $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ that are cuspidal constituents for `pins` and $\xi$ (a cuspidal subrepresentation, nonzero, and minimal among nonzero cuspidal subrepresentations), that contain a nonzero form satisfying `IsIsotypicCuspFormAt F pins ξ N S Ψ`, and that meet `archCutSubmodule F tys` nontrivially.
--
--   This is the representation-theoretic half of the discrete decomposition of the cuspidal spectrum of $\mathrm{GL}_2$ over a number field, in the edition where the level family consists of the principal congruence subgroups intersected with the finite-adelic part: an archimedean-type-cut isotypic cusp form is a finite sum of vectors lying in cuspidal constituents, and only constituents compatible with the isotypic datum and the type family occur. It feeds the finite-dimensionality of the isotypic archimedean cut and the extraction of smooth Casimir eigenvectors from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isotypicCuspSubmodule_principal_inf_archCutSubmodule_le_iSup_isCuspConstituent.lean

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

theorem AutomorphicForm.isotypicCuspSubmodule_principal_inf_archCutSubmodule_le_iSup_isCuspConstituent
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ≤
      ⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ V ∧ CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ N S Ψ V ∧
              V ⊓ archCutSubmodule F tys ≠ ⊥), V := by sorry
