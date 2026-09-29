-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_finiteAdelic_of_isCuspConstituent_of_finiteDimensional_of_mem_levelInvariantSubmodule_of_mem_archCutSubmodule_ofChar_of_pos
-- name    : AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_finiteAdelic_of_isCuspConstituent_of_finiteDimensional_of_mem_levelInvariantSubmodule_of_mem_archCutSubmodule_ofChar_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/bb23a70f-d2e8-52b1-99f1-661474dcff39
-- title:
--   Finite-adelic translates of one type-χ vector span the others
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$, $0<d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_F)$; put $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\}$, the window consisting of those $g$ whose finite part is integral, whose archimedean components at every infinite place have local height $\ge c$, $x$-window square $\le u^2$ and archimedean determinant norm in $[d_1,d_2]$. Assume $D$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and a central idele $z$ with $\gamma g z\in D$. Work at the pins `productionPinsOf` attached to $D$, to the level family $N\mapsto \mathrm{levelOne}(N)\sqcap\ker(\mathrm{glArch})$, to the Hecke generators $\mathrm{heckeGen}\,v$ and to the box `adelicBox F`, whose central subgroup is all of the idele units; let $\xi$ be a character of that subgroup. Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is a cuspidal constituent for $\xi$: it satisfies the predicate `IsCuspSubrep`, it is nonzero, and every `IsCuspSubrep` submodule contained in it is $\bot$ or $V$. Assume admissibility: for every nonzero ideal $N$ and every archimedean type family `tys`, the intersection of $V$ with the $N$-level-invariant functions ($\varphi(gu)=\varphi(g)$ for $u$ in the level group) and with $\mathrm{archCutSubmodule}\,F\,\mathrm{tys}$ is finite-dimensional over $\mathbb{C}$. Assume every infinite place of $F$ is real, and let $\chi=(\chi_w)$ be characters of the groups $\mathrm{rowIsometrySubgroup}_0$ of the completions. Let $\Psi_1,\Psi_2\in V$ both lie in the archimedean cut of the one-dimensional type family $\mathrm{ArchTypeFamily.ofChar}\,F\,\chi$, let $N_1\ne 0$ be an ideal with $\Psi_1$ invariant under the level group at $N_1$, and let $\Psi_1\ne 0$. Then $\Psi_2$ lies in the $\mathbb{C}$-span of the right translates $x\mapsto\Psi_1(xg)$ with $g$ in $\ker(\mathrm{glArch})$, the finite-adelic subgroup.
--
--   This is the multiplicity-one statement, in the form used here, that inside a single admissible cuspidal constituent the vectors of one fixed one-dimensional archimedean type are generated over the finite adeles by any one nonzero such vector possessing a level; classically it reflects the factorisation $V\cong\pi_\infty\otimes\pi_f$ together with irreducibility of $\pi_f$ and the fact that each character of $\mathrm{SO}(2)$ occurs at most once in an irreducible admissible representation of $\mathrm{GL}_2(\mathbb{R})$. It is used in identifying the adelic span attached to a primitive newform via its $\Gamma_1$-lift and twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_finiteAdelic_of_isCuspConstituent_of_finiteDimensional_of_mem_levelInvariantSubmodule_of_mem_archCutSubmodule_ofChar_of_pos.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_finiteAdelic_of_isCuspConstituent_of_finiteDimensional_of_mem_levelInvariantSubmodule_of_mem_archCutSubmodule_ofChar_of_pos
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (hadm : ∀ (N : Ideal (𝓞 F)) (tys : ArchTypeFamily F), N ≠ ⊥ →
      FiniteDimensional ℂ
        ↥(V ⊓ levelInvariantSubmodule F
              (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
              N ⊓
            archCutSubmodule F tys))
    (hreal : ∀ w : InfinitePlace F, w.IsReal)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (Ψ₁ Ψ₂ : AdelicGL2 (𝓞 F) F → ℂ) (h₁ : Ψ₁ ∈ V) (h₂ : Ψ₂ ∈ V)
    (hχ₁ : Ψ₁ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (hχ₂ : Ψ₂ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (N₁ : Ideal (𝓞 F)) (hN₁ : N₁ ≠ ⊥)
    (h₁N : Ψ₁ ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N₁)
    (hne : Ψ₁ ≠ 0) :
    Ψ₂ ∈ Submodule.span ℂ
      ((fun g => rightTranslate F g Ψ₁) '' (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))) := by sorry
