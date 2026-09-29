-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut
-- name    : AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/43b5e4dd-04fe-5586-a723-807a41ea0ab4
-- title:
--   Iterated archimedean derivatives of cut vectors: smoothness and continuity
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $D=\bigcup_{y\in T}\,\{g y : g\in \mathrm{Siegel}\}$, where $\mathrm{Siegel}=$ `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite part is integral, whose archimedean component at every infinite place has local height at least $c$ and window square $x$-coordinate at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$. Assume $D$ covers modulo the centre, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ satisfies $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(K)$ (via global points) and some central adelic scalar $z$. Fix the carrier data `productionPinsOf` attached to $D$, to the level subgroups $N\mapsto$ `levelOne` $(N)\sqcap$ `finiteAdelicGL2Subgroup` (the kernel of the archimedean projection), to the Hecke generators `heckeGen` at the finite places, and to the adelic box; let $\xi$ be a homomorphism from its central subgroup $\top$ to $\mathbb{C}^\times$, and let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ that is a cuspidal constituent for these data and $\xi$: $V$ satisfies the predicate `IsCuspSubrep`, is non-zero, and every `IsCuspSubrep` submodule contained in $V$ is $\bot$ or $V$. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let `tys` be an archimedean type family (a cardinality function on infinite places together with that many representations at each place), and let $x$ lie in the intersection of $V$, of the submodule of functions invariant under right translation by the level subgroup at $N$, and of `archCutSubmodule K tys` (the intersection over infinite places $w$ of the sum of the submodules `archTypeSubmoduleAt` for the types listed at $w$). Then for every real infinite place $w$ and every list $l$ of directions in $\{H,E,F\}$, the iterated derivative $l.\mathrm{foldr}\,(\mathrm{archDerivAt}\ hw)\ x$, each step sending $\varphi$ to $g\mapsto \tfrac{d}{dt}\varphi(g\cdot \mathrm{archFlowAt}\,hw\,d\,t)|_{t=0}$, is archimedean-smooth at $w$ — for every $g$ the map $e\mapsto \varphi(g\cdot \mathrm{archRealLiftAt}\,hw\,e)$ is $C^\infty$ on the set of real $2\times 2$ matrices of non-zero determinant — and is continuous on $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is the regularity statement for vectors in the level-and-type cut of a cuspidal constituent: all iterated derivatives along the archimedean one-parameter flows at a real place exist as smooth, continuous functions, so that the Casimir operator and the raising and lowering operators may be applied freely to such vectors. It is the analytic input for the subsequent identification of the archimedean behaviour of cut vectors (Casimir eigenvalue reality and non-vanishing of the lowering direction) and for the assembly of the core hypotheses on cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut.lean

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

theorem AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut
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
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w : InfinitePlace K) (hw : w.IsReal) (l : List ArchDir) :
    IsArchSmoothAt hw (l.foldr (archDerivAt hw) x) ∧ Continuous (l.foldr (archDerivAt hw) x) := by sorry
