-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent
-- name    : AlgebraicGeometry.OModulePresheaf.ker_d_succ_le_range_d_of_isQuasicoherent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/13381d64-b7a7-5844-a54e-9b369102356f
-- title:
--   Affine Čech acyclicity for quasi-coherent module presheaves
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme, and $\pi\colon V \to \operatorname{Spec} R$ a morphism, with $V$ affine and $\pi$ separated. Let $F$ be an `OModulePresheaf` over $\pi$: an assignment to each open $U \subseteq V$ of a type $F(U)$ carrying an abelian group structure together with a module structure over $R$ and over $\Gamma(V,U)$, compatible via the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, and, for each inclusion $U \le U'$, an $R$-linear restriction map $F(U') \to F(U)$ satisfying $\operatorname{res}(a \cdot x) = (a|_U) \cdot \operatorname{res}(x)$ for $a \in \Gamma(V,U')$, with restriction along the identity being the identity and restriction along a composite being the composite; no sheaf condition is imposed. Assume $F$ is quasi-coherent in the elementwise sense that for every affine open $U$ of $V$ and every $f \in \Gamma(V,U)$: each $x \in F(V_f)$, where $V_f$ is the basic open of $f$, satisfies $\operatorname{res}(y) = (f^n|_{V_f}) \cdot x$ for some $n \in \mathbb{N}$ and $y \in F(U)$; and any $y \in F(U)$ restricting to $0$ in $F(V_f)$ is killed by $f^n$ for some $n$. Let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type $\iota$ together with opens $U_i$, each affine, with $\bigsqcup_i U_i = \top$, and let $i \in \mathbb{N}$. Then, in the Čech complex `F.d K` attached to $F$ and $K$, the kernel of the differential in degree $i+1$ is contained in the image of the differential in degree $i$.
--
--   This is the vanishing of the higher Čech cohomology of a quasi-coherent module datum on an affine scheme with respect to a finite ordered affine cover, in the form of an inclusion of submodules in each degree $\ge 1$ (nothing is asserted in degree $0$). It feeds the exactness of the rows and columns of the iterated Čech bicomplex and the degree-zero statement over a basic open.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.ker_d_succ_le_range_d_of_isQuasicoherent
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsAffine V] [IsSeparated π]
    (F : OModulePresheaf π) (hF : F.IsQuasicoherent) (K : V.OrderedAffineCover) (i : ℕ) :
    LinearMap.ker (F.d K (i + 1)) ≤ LinearMap.range (F.d K i) := by sorry
