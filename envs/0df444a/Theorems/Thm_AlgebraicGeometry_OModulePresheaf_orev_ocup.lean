-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_orev_ocup
-- name    : AlgebraicGeometry.OModulePresheaf.orev_ocup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/48fdd217-d737-5127-862e-bb55d7548c40
-- title:
--   Reversal anti-commutes with the ordered cup product
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi : V \to \operatorname{Spec} R$ a morphism, and let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq V$, each affine, whose supremum is $\top$. For $m \in \mathbb{N}$ write $\mathrm{OIdx}\,m = (\mathrm{Fin}(m+1) \to \iota)$ and, for such a tuple $t$, $U_t = \bigsqcap_j U_{t(j)}$; an $m$-cochain of the presheaf `OModulePresheaf.unit π` (the structure sheaf, viewed as a presheaf of $R$-modules via $\pi$) is a family assigning to each $t$ an element of $\Gamma(V, U_t)$. Given $a, b, n$ with $a+b=n$ and cochains $\alpha$ of degree $a$, $\beta$ of degree $b$, the assertion is the identity of $n$-cochains $$\mathrm{orev}_n(\alpha \smile \beta) = (-1)^{ab} \cdot \bigl(\mathrm{orev}_b\,\beta \smile \mathrm{orev}_a\,\alpha\bigr),$$ the right-hand cup product being formed with the equality $b+a=n$ and the sign acting as an integer scalar. Here $(\alpha \smile \beta)(t)$ is the product in $\Gamma(V, U_t)$ of the restrictions of $\alpha$ on the front face $j \mapsto t(j)$ ($j \le a$) and of $\beta$ on the back face $j \mapsto t(a+j)$, and $(\mathrm{orev}_m\gamma)(t) = (-1)^{m(m+1)/2}$ times the restriction of $\gamma(t \circ \mathrm{rev})$ to $U_t$.
--
--   This is the graded (Koszul-sign) anti-commutation of the reversal operator with the ordered Alexander–Whitney cup product on the ordered Čech complex of the structure sheaf of $V$ over $\operatorname{Spec} R$. It is the computational input to [`AlgebraicGeometry.OModulePresheaf.cls_mul_comm_graded`](thm.html#AlgebraicGeometry.OModulePresheaf.cls_mul_comm_graded), where graded commutativity of the induced product on cohomology classes is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_orev_ocup.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechReversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.orev_ocup
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))
    (K : V.OrderedAffineCover) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit π).ocochain K a) (β : (OModulePresheaf.unit π).ocochain K b) :
    (OModulePresheaf.unit π).orev K n ((OModulePresheaf.unit π).ocup K a b n hn α β) =
      ((-1 : ℤ) ^ (a * b)) • (OModulePresheaf.unit π).ocup K b a n (by omega)
        ((OModulePresheaf.unit π).orev K b β) ((OModulePresheaf.unit π).orev K a α) := by sorry
