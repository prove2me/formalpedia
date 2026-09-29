-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/7f23e686-5d45-561a-a198-cda46669a592
-- title:
--   A single Casimir eigenvalue on a cuspidal constituent
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $K$. Put $D=\bigcup_{x\in T}\{g x : g\in \mathtt{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\}$, where the latter set consists of those adelic matrices whose finite part lies in `finiteIntegralGL2` and whose archimedean component at every infinite place has local height at least $c$, squared $x$-window at most $u^2$ and archimedean determinant norm in $[d_1,d_2]$; it is assumed that $D$ covers modulo the centre, i.e. every adelic $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g z\in D$. The carrier data are `productionPinsOf` for $D$, with level subgroups $N\mapsto \mathtt{levelOne}\,N\sqcap\mathtt{finiteAdelicGL2Subgroup}$ (the latter the kernel of the archimedean projection), Hecke generators $v\mapsto\mathtt{heckeGen}\,v$, and the box `adelicBox`; its central subgroup is all of the idele unit group, and $\xi$ is a character of it. Let $V$ be a $\mathbb{C}$-submodule of the functions on adelic $\mathrm{GL}_2$ which is a cuspidal constituent for these data and $\xi$: it satisfies the predicate `IsCuspSubrep`, is non-zero, and every `IsCuspSubrep` submodule contained in it is $\bot$ or $V$. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$ and `tys` an archimedean type family (a number $\mathrm{card}(v)$ of archimedean representations at each infinite place $v$), and assume the intersection of $V$, the submodule of functions right-invariant under $\mathtt{levelOne}\,N\sqcap\mathtt{finiteAdelicGL2Subgroup}$, and the archimedean cut submodule $\bigsqcap_v\bigsqcup_i \mathtt{archTypeSubmoduleAt}\,v\,(\mathtt{tys.rep}\,v\,i)$ is non-zero. Finally let $w$ be a real infinite place of $K$. Then there is a single $\lambda\in\mathbb{C}$ such that every $x\in V$ is archimedean-smooth at $w$ (for each $g$, the function $e\mapsto x(g\cdot\mathtt{archRealLiftAt}\,hw\,e)$ on real $2\times 2$ matrices is $C^\infty$ on the locus of non-vanishing determinant), all three first derivatives $D_H x, D_E x, D_F x$ (each defined as the derivative at $t=0$ of $t\mapsto x(g\cdot\mathtt{archFlowAt}\,hw\,d\,t)$) are continuous, all nine second derivatives $D_d D_{d'} x$ are continuous, and $-\bigl(\tfrac14 D_HD_H x-\tfrac12 D_H x+D_ED_F x\bigr)=\lambda\, x$.
--
--   This is Schur's lemma for the Casimir element of $\mathfrak{gl}_2(\mathbb{R})$ at a real place, stated at the level of functions: the cuspidal constituent $V$ has a single infinitesimal Casimir eigenvalue at $w$, together with the regularity needed for the differential operators to be defined. It feeds the construction of isotypic cusp forms and the core hypotheses packages attached to cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsReal) :
    ∃ lam : ℂ, ∀ x ∈ V, IsArchSmoothAt hw x ∧ (∀ d : ArchDir, Continuous (archDerivAt hw d x)) ∧
      (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) ∧ archCasimirAt hw x = lam • x := by sorry
