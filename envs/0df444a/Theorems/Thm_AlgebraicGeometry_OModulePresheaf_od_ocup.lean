-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_od_ocup
-- name    : AlgebraicGeometry.OModulePresheaf.od_ocup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/bca2d97b-bc81-5127-9ca6-c8693707ca9e
-- title:
--   Leibniz rule for the ordered Čech cup product
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme with a morphism $\pi : V \to \operatorname{Spec} R$, and $F$ an `OModulePresheaf` over $\pi$: an assignment $U \mapsto F.obj\,U$ of $R$-modules to the opens of $V$, each also a module over $\Gamma(V,U)$ compatibly with the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restriction maps $F.res : F.obj\,U' \to F.obj\,U$ for $U \le U'$ that are semilinear for the presheaf restriction on sections and satisfy the identity and composition laws. Let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type $\iota$, opens $U_i$ that are affine and satisfy $\bigsqcup_i U_i = \top$. For $m \in \mathbb{N}$ an $m$-cochain assigns to each $t : \mathrm{Fin}(m+1) \to \iota$ an element of $F.obj(\bigwedge_j U_{t(j)})$; the differential `od` is the alternating sum $\sum_{j} (-1)^j$ of restrictions along the faces $t \circ \mathrm{Fin.succAbove}\,j$, and for $a+b=n$ the product `ocup` sends $(\alpha,\beta)$ to the cochain whose value at $t$ is the restriction of $\alpha$ at the front face $j \mapsto t(j)$, $j \le a$, acting by the $\Gamma$-module structure on the restriction of $\beta$ at the back face $j \mapsto t(a+j)$. Given naturals $a,b,n$ with $a+b=n$, an $a$-cochain $\alpha$ for the unit presheaf $U \mapsto \Gamma(V,U)$, and a $b$-cochain $\beta$ for $F$, the conclusion is $$d(\alpha \smile \beta) = (d\alpha) \smile \beta + (-1)^a\,\alpha \smile (d\beta),$$ the two products on the right being formed with the decompositions $(a+1)+b = n+1$ and $a+(b+1) = n+1$.
--
--   This is the Leibniz rule making the ordered Čech cochain complex of $F$ a graded module over the ordered Čech cochain algebra of the structure presheaf, for the Alexander–Whitney (front face/back face) cup product. It is used in establishing graded commutativity of the induced product on cohomology classes and in the comparison of cup products with the unit pullback on kernels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_od_ocup.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.od_ocup
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit π).ocochain K a) (β : F.ocochain K b) :
    F.od K n (F.ocup K a b n hn α β) =
      F.ocup K (a + 1) b (n + 1) (by omega) ((OModulePresheaf.unit π).od K a α) β +
        ((-1 : ℤ) ^ a) • F.ocup K a (b + 1) (n + 1) (by omega) α (F.od K b β) := by sorry
