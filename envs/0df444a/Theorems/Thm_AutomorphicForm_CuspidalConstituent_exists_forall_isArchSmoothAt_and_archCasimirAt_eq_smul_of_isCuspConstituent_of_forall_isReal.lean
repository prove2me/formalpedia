-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_forall_isReal
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_forall_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/a496eb8f-36f7-56c5-9d8d-df273fcf1f3e
-- title:
--   Casimir acts by a scalar on a totally real cuspidal constituent
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $K$. Write $D=\bigcup_{x\in T}\,(\cdot\,*x)''\,\mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2$, the union of the right translates by the elements of $T$ of the set of $g$ whose finite part is integral, whose local height at every infinite place is at least $c$, whose $x$-window square at every infinite place is at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$; assume `CoversModCentre`, i.e. every adelic $g$ can be moved into $D$ by left multiplication by a global point of $\mathrm{GL}_2(K)$ and right multiplication by a central adelic scalar. Let `pins` be the production carrier data on $D$ with level subgroups $U(N)=\mathrm{levelOne}\,N\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}$ and box $\mathrm{adelicBox}$, let $\xi$ be a homomorphism from `pins.Z` (here the full unit group) to $\mathbb{C}^\times$, and let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data: $V$ is a cusp subrepresentation, $V\neq 0$, and every cusp subrepresentation contained in $V$ is $0$ or $V$. Assume further: $N$ is a non-zero ideal of $\mathcal{O}_K$; `tys` is an archimedean type family, assigning to each infinite place a finite list of archimedean representations; the intersection of $V$ with the submodule of functions invariant under right translation by $U(N)$ and with the archimedean cut submodule $\bigsqcap_w \bigsqcup_i$ of the type submodules is non-zero; every infinite place of $K$ is real; and $w$ is an infinite place with $hw$ a proof that $w$ is real. Then there exists $\lambda\in\mathbb{C}$ such that every $x\in V$ is archimedean-smooth at $w$ (for each $g$, the function $e\mapsto x(g\cdot \mathrm{archRealLiftAt}\,hw\,e)$ is $C^\infty$ on the set of invertible real $2\times2$ matrices), all first derivatives $\mathrm{archDerivAt}\,hw\,d\,x$ for $d\in\{H,E,F^-\}$ are continuous, all second derivatives $\mathrm{archDerivAt}\,hw\,d\,(\mathrm{archDerivAt}\,hw\,d'\,x)$ are continuous, and $$-\Bigl(\tfrac14 D_HD_H-\tfrac12 D_H+D_ED_{F^-}\Bigr)x=\lambda\, x,$$ i.e. $\mathrm{archCasimirAt}\,hw\,x=\lambda\cdot x$. The same scalar $\lambda$ works for all $x\in V$.
--
--   This is Schur's lemma for the Casimir element at a real place, realised at the level of functions: a cuspidal constituent has a single infinitesimal Casimir eigenvalue at $w$, together with the regularity needed to apply the archimedean differential calculus. It is the totally real case, used in the derivation of the corresponding statement for a cuspidal constituent without the assumption that all infinite places are real.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_forall_isReal.lean

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

theorem AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_forall_isReal
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
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (w : InfinitePlace K) (hw : w.IsReal) :
    ∃ lam : ℂ, ∀ x ∈ V, IsArchSmoothAt hw x ∧ (∀ d : ArchDir, Continuous (archDerivAt hw d x)) ∧
      (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) ∧ archCasimirAt hw x = lam • x := by sorry
