-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_unit_of_isSeparated
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_unit_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/772aaa43-8554-5be8-ab5f-5ef051bcc827
-- title:
--   Cover-independence of Čech cohomology of mathcal O_V
-- statement:
--   Let $R$ be a commutative ring, let $V$ be a scheme and let $\pi : V \to \operatorname{Spec} R$ be a separated morphism, and let $K$, $K'$ be two ordered affine covers of $V$, each consisting of a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq V$ that are affine and satisfy $\bigsqcup_i U_i = \top$. Consider the $\mathcal O$-module presheaf `OModulePresheaf.unit π`: it assigns to an open $U$ the ring of sections $\Gamma(V, U)$, viewed as an $R$-module through the $R$-algebra structure that $\pi$ induces on $\Gamma(V,U)$ and as a module over $\Gamma(V,U)$ by multiplication, with restriction maps the presheaf restrictions of $V$. For an ordered affine cover $K$ its alternating Čech complex has degree-$i$ cochains $\prod_{s \,:\, K.\mathrm{Idx}\, i} \Gamma(V, K.\mathrm{inter}\, s)$, with differential `d`, and one puts $H^0 = \ker(d_0)$ and, for $i : \mathbb{N}$, $H^{i+1} = \ker(d_{i+1}) / \operatorname{im}(d_i)$. The assertion is that there exists an $R$-linear isomorphism between the $H^0$ computed from $K$ and the one computed from $K'$, and that for every $i : \mathbb{N}$ there exists an $R$-linear isomorphism between the corresponding $H^{i+1}$ groups. The isomorphisms are asserted only to exist, as `Nonempty` statements, with no compatibility or canonicity claimed.
--
--   This is the independence of alternating Čech cohomology of the structure sheaf from the chosen finite affine open cover, for a scheme separated over an affine base. It is used in the study of cohomology of Jacobians in the good-reduction argument, where vanishing of the higher Čech groups of $\mathcal O_V$ for one convenient cover is transferred to an arbitrary ordered affine cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_unit_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_unit_of_isSeparated
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
    (K K' : V.OrderedAffineCover) :
    Nonempty ((OModulePresheaf.unit π).H0 K ≃ₗ[R] (OModulePresheaf.unit π).H0 K') ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.unit π).HSucc K i ≃ₗ[R] (OModulePresheaf.unit π).HSucc K' i) := by sorry
