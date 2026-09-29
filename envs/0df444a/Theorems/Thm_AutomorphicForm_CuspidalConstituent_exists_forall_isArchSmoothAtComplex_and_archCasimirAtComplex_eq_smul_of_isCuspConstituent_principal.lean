-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent_principal
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/05594d21-1b1c-5d43-862c-48314e355efc
-- title:
--   Casimirs at a complex place act by scalars on a cuspidal constituent, principal level
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$, $0<d_1$ and $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Assume the union $D=\bigcup_{x\in T}(\cdot\, x)[\,\mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\,]$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}_K^{\times}$ with $\gamma g z\in D$, where the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose archimedean component at each infinite place has local height at least $c$ and window $\le u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$. Form the carrier data `productionPinsOf` on $D$ with level family $N\mapsto \mathrm{principalLevel}(N)\sqcap\ker(\mathrm{glArch})$, Hecke generators $v\mapsto \mathrm{heckeGen}_v$ and the box $\mathrm{adelicBox}$; its central subgroup is all of $\mathbb{A}_K^{\times}$, and $\xi$ is a character of it into $\mathbb{C}^{\times}$. Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data and $\xi$: $V$ lies in the cuspidal $K$-finite submodule, is stable under right translation by the finite-adelic subgroup and by the row-isometry subgroups at all infinite places and under right convolution by factorizable archimedeanly bi-finite test functions, is non-zero, and contains no cusp subrepresentation other than $0$ and $V$. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$ and $\mathrm{tys}$ a family of archimedean types, and assume the intersection of $V$ with the submodule of functions invariant under right multiplication by $\mathrm{principalLevel}(N)\sqcap\ker(\mathrm{glArch})$ and with the archimedean type cut $\bigsqcap_w\bigsqcup_i \mathrm{archTypeSubmoduleAt}$ is non-zero. Let $w$ be a complex place of $K$. Then there are scalars $\lambda,\lambda'\in\mathbb{C}$, independent of the vector, such that every $x\in V$ is smooth at $w$ (for each $g$ the map $e\mapsto x(g\cdot\mathrm{archComplexLiftAt}\,e)$ is $C^{\infty}$ on the invertible matrices), all first derivatives $D_d x$ along the six flow directions $H,E,F,iH,iE,iF$ at $w$ are continuous, all second derivatives $D_d D_{d'} x$ are continuous, and, with $\partial_X=\tfrac12(D_X-iD_{iX})$ and $\bar\partial_X=\tfrac12(D_X+iD_{iX})$, the two operators $\Omega_w=-\bigl(\tfrac14\partial_H^2-\tfrac12\partial_H+\partial_E\partial_F\bigr)$ and $\bar\Omega_w$ (the same expression in the $\bar\partial$'s) satisfy $\Omega_w x=\lambda x$ and $\bar\Omega_w x=\lambda' x$.
--
--   This is the statement that the two Casimir elements attached to a complex place act by a single pair of scalars on an irreducible cuspidal constituent, together with the smoothness and continuity of first and second flow derivatives needed for those operators to be defined on all of $V$; it is the edition of the result for the principal congruence level family $N\mapsto K(N)$ met with the finite-adelic subgroup. It feeds the determination of archimedean Casimir eigenvalues on isotypic cuspidal submodules cut by a level and an archimedean type family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent_principal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent_principal
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsComplex) :
    ∃ lam lam' : ℂ, ∀ x ∈ V, IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
      (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧
      archCasimirAtComplex hw x = lam • x ∧ archCasimirBarAtComplex hw x = lam' • x := by sorry
