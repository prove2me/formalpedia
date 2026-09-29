-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/8733b3f9-1a6f-5183-bc53-1415d5ecadee
-- title:
--   Čech cohomology independent of the ordered affine cover
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi \colon V \to \operatorname{Spec} R$ a separated morphism, and let $M$ be a sheaf of $\mathcal O_V$-modules. Consider the presheaf of $R$-modules `OModulePresheaf.ofModules π M` which assigns to an open $U \subseteq V$ the sections $\Gamma(M,U)$, with its $\Gamma(V,U)$-module structure and the $R$-module structure obtained from it along the algebra map $R \to \Gamma(V,U)$ induced by $\pi$, and with restriction maps those of $M$. Assume this presheaf satisfies `IsQuasicoherent`: for every affine open $U$ of $V$ and every $f \in \Gamma(V,U)$, every section $x$ over the basic open $D(f)$ admits $n \in \mathbb N$ and a section $y$ over $U$ whose restriction equals $f^n|_{D(f)} \cdot x$, and every section $y$ over $U$ restricting to $0$ on $D(f)$ is killed by some power $f^n$. Let $K$ and $K'$ be two ordered affine covers of $V$, each given by a finite linearly ordered index type together with affine opens whose supremum is $\top$. The conclusion is the conjunction of: the existence of an $R$-linear isomorphism between the kernels of the degree-$0$ Čech differentials of the two covers, i.e. between $H^0$ computed from $K$ and from $K'$; and, for every $i \in \mathbb N$, the existence of an $R$-linear isomorphism between the degree-$(i+1)$ Čech cohomology modules $\ker(d_{i+1})/\operatorname{im}(d_i)$ of the two covers. The isomorphisms are asserted only to exist (`Nonempty`), with no canonicity claimed.
--
--   This is the classical independence of the alternating Čech cohomology of a quasi-coherent sheaf on a separated scheme from the chosen finite affine open cover, phrased as a direct comparison of two covers so that no derived functors enter. It underlies the later vanishing, finiteness and base-change statements for Čech cohomology, which compute with one convenient cover and then transport the answer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
    (M : V.Modules) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (K K' : V.OrderedAffineCover) :
    Nonempty ((OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 K') ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π M).HSucc K i ≃ₗ[R]
        (OModulePresheaf.ofModules π M).HSucc K' i) := by sorry
