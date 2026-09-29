-- Prove2me | Theorems.Thm_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre
-- name    : AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/f0ba5a48-0ba0-5c71-9e8d-9cac5969bb6b
-- title:
--   Strong multiplicity one for cuspidal constituents at principal level
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$: those $g$ whose finite part is finite-integral, whose archimedean component at every infinite place has local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$. Assume $D$ covers modulo the centre: every $g\in \mathrm{GL}_2(\mathbb{A}_F)$ satisfies $\gamma g z\in D$ for some $\gamma\in \mathrm{GL}_2(F)$ and some central idelic scalar $z$. Let the carrier datum be `productionPinsOf` for this $D$, for the level family $N\mapsto \mathrm{K}(N)\cap\ker(\mathrm{glArch})$ given by `principalLevel` met with the finite-adelic subgroup, for the Hecke coset generators `heckeGen` at the finite places, and for the conditional adelic additive Haar measure on `adelicBox`; its central subgroup is all of $(\mathbb{A}_F)^\times$, its measure the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$. Let $\xi$ be a character of that central subgroup with values in $\mathbb{C}^\times$, let $N$ be an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, and $\Psi$ a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with families $a_v,b_v$ of complex numbers). Let $V_1,V_2$ be $\mathbb{C}$-submodules of the functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$, each a cuspidal constituent for this datum and $\xi$, that is: contained in the $K$-finite cusp submodule, stable under right translation by finite-adelic elements and by the row-isometry subgroups at the infinite places and under right convolution by factorizable, archimedean bi-finite test functions; nonzero; and minimal, in that every such stable subspace contained in it is $\bot$ or the whole space. Assume further that each $V_i$ contains a nonzero $\varphi$ which is an isotypic cusp form for the data $(\xi,N,S,\Psi)$: a smooth cuspidal automorphic function of central character $\xi$, continuous, invariant under right translation by the level subgroup at $N$, an eigenfunction of the Hecke coset operator at every $v\notin S$ with eigenvalue $\Psi.a\,v$, and satisfying the central relation with factor $\Psi.b\,v$ for every $v\notin S$. Then $V_1=V_2$.
--
--   This is the principal-congruence-level form of strong multiplicity one for cuspidal representations of $\mathrm{GL}_2$ over a number field: a cofinite system of Hecke eigenvalues together with a central character determines at most one cuspidal constituent containing a nonzero vector of level $\mathrm{K}(N)$. It is used to show that the cuspidal constituents meeting a given eigensystem datum lie under the supremum of finitely many constituents, and in the analysis of isotypic cusp spaces intersected with archimedean cut submodules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (h₁ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ V₁)
    (h₂ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ V₂)
    (m₁ : AutomorphicForm.CuspidalConstituent.CuspConstituentMeets F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ N S Ψ V₁)
    (m₂ : AutomorphicForm.CuspidalConstituent.CuspConstituentMeets F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ N S Ψ V₂) :
    V₁ = V₂ := by sorry
