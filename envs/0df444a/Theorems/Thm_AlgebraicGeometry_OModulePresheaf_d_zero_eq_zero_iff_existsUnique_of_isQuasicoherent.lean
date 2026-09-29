-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent
-- name    : AlgebraicGeometry.OModulePresheaf.d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/059c5c01-d82d-5a05-9f9c-d569aeb59230
-- title:
--   Degree-zero Čech cocycles are global sections
-- statement:
--   Fix a commutative ring $R$ and a scheme $V$ equipped with a morphism $\pi : V \to \operatorname{Spec} R$, with $V$ affine and $\pi$ separated. Let $F$ be an `OModulePresheaf` for $\pi$: an assignment of an $R$-module $F(U)$ to each open $U \subseteq V$, carrying compatible $\Gamma(V,U)$-module structures over the $R$-algebra structure induced by $\pi$, together with $R$-linear restriction maps $F(U') \to F(U)$ for $U \le U'$ that are semilinear for restriction of functions and satisfy the identity and composition laws. Assume $F$ satisfies `IsQuasicoherent`: for every affine open $U$ of $V$ and every $f \in \Gamma(V,U)$, each element $x$ of $F(V.\mathrm{basicOpen}\,f)$ equals, after multiplication by the restriction of some power $f^n$, the restriction of some $y \in F(U)$, and each $y \in F(U)$ restricting to $0$ on the basic open set is annihilated by some power $f^n$. Let $K$ be an ordered affine cover of $V$, i.e. a finite linearly ordered index type $\iota$ with affine opens $U_i$ whose supremum is $\top$, and let $c$ be a $0$-cochain, assigning to each strictly monotone $s : \mathrm{Fin}\,1 \to \iota$ an element $c_s$ of $F$ on the intersection $\bigsqcap_j U_{s(j)}$. Then the Čech differential satisfies $d^0 c = 0$ if and only if there is a unique $x \in F(\top)$ whose restriction to each such intersection is $c_s$.
--
--   This is the degree-zero case of the comparison between Čech cohomology of an affine cover and global sections: for quasi-coherent data the augmentation $F(V) \to \check{H}^0(K,F)$ is bijective, the $0$-cocycle condition being exactly the gluing condition. It is used in the proof that the Čech pushforward is bijective over affine preimages and in the row-exactness of the iterated Čech double complex for quasi-coherent data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsAffine V] [IsSeparated π]
    (F : OModulePresheaf π) (hF : F.IsQuasicoherent) (K : V.OrderedAffineCover) (c : F.cochain K 0) :
    F.d K 0 c = 0 ↔ ∃! x : F.obj ⊤, ∀ s : K.Idx 0, c s = F.res le_top x := by sorry
