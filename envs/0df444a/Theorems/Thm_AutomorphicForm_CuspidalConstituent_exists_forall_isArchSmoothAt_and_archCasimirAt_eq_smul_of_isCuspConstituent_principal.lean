-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_principal
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/5457b695-143c-5e73-b5bb-189d2c9e0244
-- title:
--   Casimir at a real place acts by a scalar on a cuspidal constituent
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $D=\bigcup_{x\in T}(\,\cdot\,*x)''$ of the centre-cut Siegel set $\mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2$, i.e. the union of the right translates by elements of $T$ of the set of $g$ whose finite part is integral, whose archimedean component at each infinite place has local height at least $c$ and squared window coordinate at most $u^2$, and whose archimedean determinant norm at each infinite place lies in $[d_1,d_2]$. Assume `CoversModCentre K D`: every $g$ can be moved into $D$ by multiplying on the left by a global point and on the right by a central idelic scalar. Let `pins` be `productionPinsOf K D` with level family $N\mapsto \mathrm{principalLevel}(\mathcal O_K,K,N)\sqcap$ `finiteAdelicGL2Subgroup K`, Hecke generators $v\mapsto \mathrm{heckeGen}$, and box `adelicBox K`; let $\xi$ be a character of `pins.Z` with values in $\mathbb{C}^\times$, and let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data: $V$ satisfies `IsCuspSubrep`, $V\neq\bot$, and every $W\le V$ satisfying `IsCuspSubrep` is $\bot$ or $V$. Assume further that for some non-zero ideal $N$ of $\mathcal O_K$ and some archimedean type family `tys` (assigning to each infinite place $w$ a number `card w` of types `rep w i`) the intersection of $V$ with the submodule of functions invariant under right translation by $\mathrm{principalLevel}(\mathcal O_K,K,N)\sqcap$ `finiteAdelicGL2Subgroup K` and with the archimedean cut submodule $\bigsqcap_w\bigsqcup_i$ `archTypeSubmoduleAt` is non-zero. Finally let $w$ be a real infinite place of $K$. Then there is a single $\lambda\in\mathbb{C}$ such that every $x\in V$ is archimedean-smooth at $w$ (for each $g$, the function $e\mapsto x(g\cdot \mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on the invertible real $2\times2$ matrices), all first derivatives $\mathrm{archDerivAt}\,d\,x$ and all second derivatives $\mathrm{archDerivAt}\,d(\mathrm{archDerivAt}\,d'\,x)$ for $d,d'\in\{H,E,F\}$ are continuous, and $\mathrm{archCasimirAt}\,x=-\bigl(\tfrac14 D_HD_H-\tfrac12 D_H+D_ED_F\bigr)x=\lambda\cdot x$.
--
--   This is the form of Schur's lemma for the Casimir element of $\mathfrak{gl}_2$ at a real place: the Casimir operator acts on an irreducible cuspidal constituent through a single eigenvalue, together with the smoothness and continuity of first and second derivatives needed for the operator to be defined on all of $V$. It is the principal-level ($K(N)$) version, and feeds the corresponding statement for members of the isotypic cusp submodule cut by level and archimedean type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_principal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_principal
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
    (w : InfinitePlace K) (hw : w.IsReal) :
    ∃ lam : ℂ, ∀ x ∈ V, IsArchSmoothAt hw x ∧ (∀ d : ArchDir, Continuous (archDerivAt hw d x)) ∧
      (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) ∧ archCasimirAt hw x = lam • x := by sorry
