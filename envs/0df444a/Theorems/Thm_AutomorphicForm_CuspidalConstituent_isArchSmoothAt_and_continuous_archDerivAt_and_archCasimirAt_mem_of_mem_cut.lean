-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut
-- name    : AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/80a2720d-aa83-54b1-bc57-1430252e64eb
-- title:
--   Vectors in a level-and-type cut are smooth; the Casimir preserves it
-- statement:
--   Let $K$ be a number field and let $c,u,d_1,d_2$ be reals with $c>0$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{x\in T}(\,\cdot\,x)[\,\mathrm{centreCutSiegelSet}\;K\,c\,u\,d_1\,d_2\,]$, the union of the right translates by elements of $T$ of the set of $g$ whose finite part is integral, whose archimedean components at every infinite place have local height $\ge c$ and $x$-window square $\le u^2$, and whose archimedean determinant norms all lie in $[d_1,d_2]$; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo global points and central scalars. Fix the carrier data $\mathrm{productionPinsOf}$ over $D$ with level subgroups $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}$ and the adelic box, and a character $\xi$ of its central group (which is $\top$). Let $V$ be a submodule of $\mathbb{C}$-valued functions on $\mathrm{GL}_2(\mathbb{A}_K)$ that is a cuspidal constituent for these data and $\xi$, i.e. $V$ satisfies `IsCuspSubrep`, is non-zero, and every `IsCuspSubrep` submodule contained in $V$ is $\bot$ or $V$. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let $\mathrm{tys}$ be an archimedean type family (a finite family of representations $\mathrm{rep}\,w\,i$, $i<\mathrm{card}\,w$, at each infinite place), let $w$ be a real place, and let $x$ lie in the cut $V\cap\{\varphi:\varphi(gu)=\varphi(g)\ \forall g,\ \forall u\in U(N)\}\cap\bigcap_w\bigvee_i \mathrm{archTypeSubmoduleAt}\,w\,(\mathrm{rep}\,w\,i)$. Then $x$ is arch-smooth at $w$, that is, for every $g$ the map $e\mapsto x(g\cdot\mathrm{archRealLiftAt}\,hw\,e)$ is $C^\infty$ on $\{e:\det e\neq0\}$; for each direction $d\in\{H,E,F\}$ the derivative $\mathrm{archDerivAt}\,hw\,d\,x$ is continuous, as is each second derivative $\mathrm{archDerivAt}\,hw\,d(\mathrm{archDerivAt}\,hw\,d'\,x)$; and the Casimir $-\bigl(\tfrac14 D_HD_H x-\tfrac12 D_H x+D_ED_F x\bigr)$ at $w$ again lies in the same cut.
--
--   This is the smoothing-and-Casimir step for the finite-dimensional level-and-type cut of a cuspidal constituent of $\mathrm{GL}_2$ over a number field: it provides the archimedean differentiability needed to let the Casimir element of $U(\mathfrak{gl}_2)$ at a real place act as an endomorphism of the cut. It is used in deducing that such a cut has a common Casimir eigenvalue, via [`AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_exists_isComplex`](thm.html#AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_exists_isComplex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut
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
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :
    IsArchSmoothAt hw x ∧ (∀ d : ArchDir, Continuous (archDerivAt hw d x)) ∧
      (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) ∧
      archCasimirAt hw x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys := by sorry
