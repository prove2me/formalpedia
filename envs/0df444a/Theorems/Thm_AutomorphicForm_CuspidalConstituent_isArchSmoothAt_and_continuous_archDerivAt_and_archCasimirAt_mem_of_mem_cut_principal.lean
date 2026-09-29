-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut_principal
-- name    : AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/2ae13e59-bbf3-5afe-ab60-15015b321009
-- title:
--   Casimir preserves the level-and-type cut of a cuspidal constituent
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{x\in T}(\,\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2]$, the union of right translates by elements of $T$ of the set of $g$ whose finite part is integral, whose archimedean component at every infinite place has local height at least $c$ and $x$-window square at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$; assume `CoversModCentre K D`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in\mathrm{GL}_2(K)$ and a central idelic scalar $z$ with $\gamma g z\in D$. Let $\mathrm{pins}$ be the production carrier data on $D$ with level family $N\mapsto K(N)\cap\ker(\mathrm{glArch})$ (the principal level met with the finite-adelic subgroup), Hecke generators $\mathrm{heckeGen}$, and adelic box $\mathrm{adelicBox}\,K$; let $\xi$ be a character of $\mathrm{pins}.Z$ with values in $\mathbb{C}^\times$ and $V$ a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for $(\mathrm{pins},\xi)$: $V$ satisfies `IsCuspSubrep`, is non-zero, and every `IsCuspSubrep` submodule contained in $V$ is $\bot$ or $V$. Let $N\neq\bot$ be an ideal of $\mathcal{O}_K$, $\mathrm{tys}$ an archimedean type family, $w$ a real infinite place of $K$, and $x$ a function lying in the cut $V\sqcap\mathrm{levelInvariantSubmodule}\,K\,\mathrm{pins}\,N\sqcap\mathrm{archCutSubmodule}\,K\,\mathrm{tys}$, i.e. $x\in V$, $x(gu)=x(g)$ for all $g$ and all $u$ in the level subgroup at $N$, and $x$ lies at each infinite place in the span of the prescribed archimedean types. Then $x$ is arch-smooth at $w$ (for every $g$, $e\mapsto x(g\cdot\mathrm{archRealLiftAt}\,hw\,e)$ is $C^\infty$ on the locus of invertible real $2\times2$ matrices), for each direction $d\in\{H,E,F^-\}$ the derivative $\mathrm{archDerivAt}\,hw\,d\,x$ is continuous, all second derivatives $\mathrm{archDerivAt}\,hw\,d\,(\mathrm{archDerivAt}\,hw\,d'\,x)$ are continuous, and the Casimir value $\mathrm{archCasimirAt}\,hw\,x=-\bigl(\tfrac14 D_HD_H x-\tfrac12 D_H x+D_ED_{F^-}x\bigr)$ again lies in the same cut.
--
--   This is the principal-level ($K(N)$) form of the assertion that the level-and-type cut of a cuspidal constituent consists of vectors smooth at a real place and is stable under the Casimir operator of $\mathfrak{gl}_2$ at that place, the standard mechanism by which the Laplace eigenvalue is attached to an automorphic vector. It feeds the construction producing, for a cuspidal constituent, a common Casimir eigenvalue on the cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut_principal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut_principal
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
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :
    IsArchSmoothAt hw x ∧ (∀ d : ArchDir, Continuous (archDerivAt hw d x)) ∧
      (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) ∧
      archCasimirAt hw x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys := by sorry
