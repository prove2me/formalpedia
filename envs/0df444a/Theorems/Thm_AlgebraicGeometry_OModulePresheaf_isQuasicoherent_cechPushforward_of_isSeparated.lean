-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated
-- name    : AlgebraicGeometry.OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/1419676e-b88a-59d8-a64f-c833a01f684c
-- title:
--   Quasi-coherence of the Čech direct image along a separated morphism
-- statement:
--   Let $A$ be a commutative ring, let $q : P \to \operatorname{Spec} A$ be a separated morphism of schemes, and let $p : V' \to P$ be a separated morphism. Let $K'$ be an ordered affine cover of $V'$: a finite linearly ordered index type $\iota$ together with opens $K'_i \subseteq V'$, each affine, whose supremum is $\top$. Let $G$ be an $\mathcal O$-module presheaf datum for the composite $q \circ p$, that is, an assignment of an $A$-module $G(U)$ to each open $U \subseteq V'$ carrying also a $\Gamma(V', U)$-module structure compatible with the $A$-algebra structure on $\Gamma(V',U)$ coming from $q \circ p$, with $A$-linear restriction maps that are semilinear for presheaf restriction of sections and satisfy the reflexivity and transitivity identities. Assume $G$ is quasi-coherent in the elementwise sense: for every affine open $U \subseteq V'$ and every $f \in \Gamma(V', U)$, every element of $G(V'_f)$ becomes, after multiplication by the restriction of some power $f^n$, the restriction of an element of $G(U)$, and every element of $G(U)$ whose restriction to $V'_f$ vanishes is annihilated by some power of $f$. The conclusion is that the Čech direct image `OModulePresheaf.cechPushforward p q K' G`, which sends an open $U \subseteq P$ to the module of families $(x_i)_{i \in \iota}$ with $x_i \in G(K'_i \cap p^{-1}U)$ agreeing after restriction to $(K'_i \cap p^{-1}U) \cap (K'_j \cap p^{-1}U)$ for all $i, j$, with componentwise restriction and with $\Gamma(P,U)$ acting through $p^{\sharp}$, satisfies the same elementwise quasi-coherence condition on $P$: over an affine open $W \subseteq P$ and $f \in \Gamma(P, W)$, every cocycle over the basic open $W_f$ becomes, after multiplication by a power of $f$, the restriction of a cocycle over $W$, and a cocycle over $W$ restricting to zero over $W_f$ is killed by a power of $f$.
--
--   This is the elementwise form of the statement that the direct image of a quasi-coherent module under a separated morphism is quasi-coherent, computed through the Čech degree-zero complex for a finite affine cover of the source; separatedness of $p$ and $q$ is what makes the charts $K'_i \cap p^{-1}W$ and their pairwise intersections affine. It is used in the construction of affine homomorphisms out of Čech direct images along proper morphisms, in [`AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated
    {A : Type u} [CommRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p]
    (K' : V'.OrderedAffineCover) (G : OModulePresheaf (p ≫ q)) (hqc : G.IsQuasicoherent) :
    (OModulePresheaf.cechPushforward p q K' G).IsQuasicoherent := by sorry
