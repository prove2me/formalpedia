-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage
-- name    : AlgebraicGeometry.OModulePresheaf.bijective_cechPushforward_of_isAffineOpen_preimage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/77249db0-8948-5375-8b30-b538e6d6f83f
-- title:
--   Sections over an affine preimage are the Čech 0-cocycles
-- statement:
--   Let $A$ be a commutative ring, $P$ a scheme and $q : P \to \operatorname{Spec} A$ a separated morphism, let $V'$ be a scheme and $p : V' \to P$ a separated morphism, and let $K'$ be an ordered affine cover of $V'$: a finite, linearly ordered index type $\iota$ together with open subsets $K'_j \subseteq V'$, each affine, whose supremum is $\top$. Let $G$ be an `OModulePresheaf` for $p \gg q$, that is, an assignment of $A$-modules $G(U)$ to the opens $U$ of $V'$, each also a $\Gamma(V', U)$-module compatibly with the $A$-algebra structure coming from $p \gg q$, equipped with $A$-linear restriction maps satisfying $G.\mathrm{res}\,h(a \cdot x) = (a|_U) \cdot G.\mathrm{res}\,h(x)$, $G.\mathrm{res}$ of the identity inclusion is the identity, and functoriality. Assume $G$ is quasi-coherent in the elementwise sense: for every affine open $U \subseteq V'$ and every $f \in \Gamma(V', U)$, each section over the basic open $D(f)$ becomes the restriction of a section over $U$ after multiplication by some power $f^n$, and each section over $U$ restricting to $0$ on $D(f)$ is annihilated by some $f^n$. Let $W$ be an affine open of $P$ and assume moreover that the open $p^{-1}W \subseteq V'$ is affine. Writing $W_j := K'_j \cap p^{-1}W$ for the charts, the conclusion is the conjunction of two assertions. First, two sections $x, y \in G(p^{-1}W)$ whose restrictions to $W_j$ agree for every $j \in \iota$ are equal. Second, for every element $c$ of the value at $W$ of the Čech direct image `cechPushforward p q K' G`, that is, every family $(c_j)_{j \in \iota}$ with $c_j \in G(W_j)$ whose members have equal restrictions to $W_i \cap W_j$ for all $i, j$, there is an $x \in G(p^{-1}W)$ with $c_j$ equal to the restriction of $x$ to $W_j$ for all $j$. Thus the statement is an explicit injectivity-plus-surjectivity pair for the restriction family, rather than bijectivity of a single named map.
--
--   This is the statement that, over an affine open $W$ of $P$ whose preimage in $V'$ is again affine, the Čech direct image of a quasi-coherent module datum computes nothing new: $\check H^0$ of the cover $(K'_j \cap p^{-1}W)_j$ agrees with $G(p^{-1}W)$, the classical vanishing of higher Čech cohomology of a quasi-coherent module on an affine scheme in degree $0$ form. It rests on the absolute degree-$0$ statement [`AlgebraicGeometry.OModulePresheaf.d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent`](thm.html#AlgebraicGeometry.OModulePresheaf.d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent), and is used in establishing quasi-coherence of the Čech direct image, via [`AlgebraicGeometry.OModulePresheaf.exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.bijective_cechPushforward_of_isAffineOpen_preimage
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
    (G : OModulePresheaf (p ≫ q)) (hqc : G.IsQuasicoherent)
    (W : P.affineOpens) (hW : IsAffineOpen (p ⁻¹ᵁ W.1)) :
    (∀ x y : G.obj (p ⁻¹ᵁ W.1),
        (∀ j : K'.ι, G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) x
          = G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) y) → x = y) ∧
      ∀ c : (OModulePresheaf.cechPushforward p q K' G).obj W.1,
        ∃ x : G.obj (p ⁻¹ᵁ W.1), ∀ j : K'.ι,
          c.1 j = G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) x := by sorry
