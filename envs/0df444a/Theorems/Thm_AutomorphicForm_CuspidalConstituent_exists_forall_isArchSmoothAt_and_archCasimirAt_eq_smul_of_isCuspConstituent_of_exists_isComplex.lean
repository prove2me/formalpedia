-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_exists_isComplex
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_exists_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/ff01eacb-bc43-53a2-a610-4dc948d4bda0
-- title:
--   Casimir at a real place scales a cuspidal constituent
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adele ring of $K$. Write $D$ for the union over $x \in T$ of the right translates by $x$ of `centreCutSiegelSet K c u d₁ d₂` (those $g$ whose finite part is integral, whose archimedean components all have local height $\ge c$ and squared $x$-window $\le u^2$, and whose archimedean determinant norms all lie in $[d_1,d_2]$), and assume `CoversModCentre K D`: every $g$ can be moved into $D$ by left multiplication by a global point of $\mathrm{GL}_2(K)$ and right multiplication by an adelic central scalar. Take the carrier data `productionPinsOf` with domain $D$, level groups $N \mapsto$ `levelOne` at $N$ intersected with the kernel of the archimedean projection, Hecke generators `heckeGen`, and box `adelicBox K`; its central subgroup is all of the adelic unit group, and $\xi$ is a character of it with values in $\mathbb{C}^\times$. Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ which is a cuspidal constituent for these data and $\xi$, i.e. a non-zero cusp subrepresentation all of whose cusp subrepresentations are $\bot$ or $V$. Let $N \neq 0$ be an ideal of $\mathcal{O}_K$ and `tys` an archimedean type family (a number `card w` of archimedean representations `rep w i` at each infinite place $w$), and assume the cut $V \cap \{\varphi : \varphi(gu)=\varphi(g) \text{ for all } u \text{ in the level group at } N\} \cap$ `archCutSubmodule K tys` is non-zero. Assume $K$ has at least one complex place, and let $w$ be a real place. Then there is a single $\lambda \in \mathbb{C}$ such that every $x \in V$ is smooth at $w$ in the sense that $e \mapsto x(g \cdot \mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on the invertible locus for each $g$, has continuous first derivatives `archDerivAt hw d x` and continuous second derivatives `archDerivAt hw d (archDerivAt hw d' x)` in the three directions $H$, $E$, $F$, and satisfies $-\bigl(\tfrac14 D_H D_H - \tfrac12 D_H + D_E D_F\bigr)x = \lambda \cdot x$.
--
--   This is the Schur-type statement that the Casimir element at a real place $w$ acts on a cuspidal constituent by one scalar, so that the constituent has a well-defined infinitesimal character at $w$, here proved at the level of functions on $\mathrm{GL}_2(\mathbb{A}_K)$. It is the case in which $K$ possesses a complex place, and feeds the corresponding statement with no restriction on the infinite places of $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_exists_isComplex.lean

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

theorem AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_exists_isComplex
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
    (hcx : ∃ v : InfinitePlace K, v.IsComplex)
    (w : InfinitePlace K) (hw : w.IsReal) :
    ∃ lam : ℂ, ∀ x ∈ V, IsArchSmoothAt hw x ∧ (∀ d : ArchDir, Continuous (archDerivAt hw d x)) ∧
      (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) ∧ archCasimirAt hw x = lam • x := by sorry
