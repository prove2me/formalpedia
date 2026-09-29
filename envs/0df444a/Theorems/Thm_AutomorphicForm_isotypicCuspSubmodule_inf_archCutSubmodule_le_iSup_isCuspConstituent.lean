-- Prove2me | Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent
-- name    : AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/c7e7ef6e-bb9f-55b5-868d-cb6ac123f79d
-- title:
--   Isotypic cusp forms with archimedean cut lie in cuspidal constituents
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $F$. Put $D=\bigcup_{x\in T}\,\{g x : g\in \mathrm{centreCutSiegelSet}\}$, the union of the right translates by the elements of $T$ of the set of $g$ whose finite part is integral, each of whose archimedean components at every infinite place $w$ has local height at least $c$, has $x$-window square at most $u^2$, and has $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$. Assume `CoversModCentre`: for every adelic $g$ there are $\gamma\in \mathrm{GL}_2(F)$ and a unit ideles $z$ with $\gamma g\,z\in D$ (the central scalar acting on the right). Let $\mathrm{pins}$ be `productionPinsOf` for $D$, with level groups $N\mapsto \mathrm{levelOne}(N)\cap \ker(\mathrm{glArch})$, Hecke generators $v\mapsto \mathrm{heckeGen}_v$, adelic Haar measure on $\mathrm{GL}_2$, central subgroup $Z=\top$, and the additive adelic Haar measure conditioned on the adelic box; let $\xi:Z\to\mathbb{C}^\times$ be a character. Let $N$ be an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, $\mathrm{tys}$ an archimedean type family (a finite family $\mathrm{rep}\,w$ of representations at each infinite place), and $\Psi$ a Hecke eigensystem over $\mathbb{C}$. Then the intersection of $\mathrm{isotypicCuspSubmodule}$, the $\mathbb{C}$-span of the functions $\varphi$ with $\mathrm{IsIsotypicCuspFormAt}\,(\mathrm{pins},\xi,N,S,\Psi)$, with $\mathrm{archCutSubmodule}$, the intersection over infinite places $w$ of the sums $\bigvee_i \mathrm{archTypeSubmoduleAt}(w,\mathrm{rep}\,w\,i)$, is contained in the supremum of those submodules $V$ of $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which are cuspidal constituents for $(\mathrm{pins},\xi)$, i.e. $\mathrm{IsCuspSubrep}$ holds for $V$, $V\neq\bot$, and every cusp subrepresentation contained in $V$ is $\bot$ or $V$; which meet the datum, i.e. contain some nonzero $\varphi$ with $\mathrm{IsIsotypicCuspFormAt}\,(\mathrm{pins},\xi,N,S,\Psi)$; and for which $V\cap \mathrm{archCutSubmodule}\neq\bot$.
--
--   This is the representation-theoretic half of the discrete decomposition of the cuspidal spectrum in the vocabulary of the project: cusp forms of a fixed isotypic Hecke datum and fixed archimedean type are exhausted by the cuspidal constituents that actually meet that datum and that type family. It is used downstream to obtain finite-dimensionality and simultaneous Casimir eigenvalue statements for such spaces of cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent.lean

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

theorem AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ≤
      ⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ V ∧ CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ N S Ψ V ∧
              V ⊓ archCutSubmodule F tys ≠ ⊥), V := by sorry
