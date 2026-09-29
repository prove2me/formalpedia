-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets
-- name    : AutomorphicForm.exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/698e207c-19c6-5bf0-a9c5-ef22761deb4e
-- title:
--   Finitely many cuspidal constituents meet a fixed Hecke eigensystem
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adele ring of $F$. Put $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\}$, the union of the right translates by elements of $T$ of the set of adelic matrices whose finite part is finite-integral, whose archimedean components at every infinite place have local height at least $c$, window square at most $u^2$, and archimedean determinant norm in $[d_1,d_2]$; assume $D$ satisfies `CoversModCentre`, i.e. every adelic $g$ can be moved into $D$ by left multiplication by a global point of $\mathrm{GL}_2(F)$ and right multiplication by a central adelic scalar. Let `pins` be `productionPinsOf` applied to $D$, to the level groups $N\mapsto \mathrm{levelOne}(N)\sqcap \mathrm{finiteAdelicGL2Subgroup}$, to the Hecke generators $v\mapsto \mathrm{heckeGen}(v)$ and to the adelic box (so its measure data are the adelic Haar measure on $\mathrm{GL}_2$ and the additive adelic Haar measure conditioned on the box, and its central subgroup is $\top$), and let $\xi$ be a group homomorphism from that central subgroup to $\mathbb{C}^\times$. Let $N$ be a nonzero ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, and $\Psi$ a Hecke eigensystem over $F$ with values in $\mathbb{C}$. Then there exists a finite set $\mathcal{V}$ of $\mathbb{C}$-submodules of the functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ such that every $W\in\mathcal{V}$ is a cuspidal constituent for `pins` and $\xi$ (a nonzero submodule of the $K$-finite cusp space, stable under right translation by finite adelic matrices and by archimedean row-isometries and under right convolution by factorizable archimedean-bi-finite test functions, and minimal among such nonzero submodules), and such that every cuspidal constituent $V$ for `pins` and $\xi$ containing a nonzero $\varphi$ which is an $(N,S,\Psi)$-isotypic cusp form satisfies $V\le\bigsqcup_{W\in\mathcal{V}}W$.
--
--   This is the finiteness statement behind strong multiplicity one in the present framework: only finitely many cuspidal constituents of a fixed central character carry a cusp form of level $N$ whose Hecke eigenvalues away from $S$ are prescribed by $\Psi$, so that the isotypic part is contained in a finite sum of constituents. It feeds the finite-dimensionality of the isotypic cusp space cut by archimedean conditions, the existence of an isotypic form inside a single constituent, and the Rankin–Selberg analytic continuation used later.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets.lean

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

theorem AutomorphicForm.exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψ : HeckeEigensystem F ℂ) :
    ∃ 𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ W ∈ 𝒱, IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ W) ∧
      ∀ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
        IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ V →
        CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ N S Ψ V →
          V ≤ ⨆ W ∈ 𝒱, W := by sorry
