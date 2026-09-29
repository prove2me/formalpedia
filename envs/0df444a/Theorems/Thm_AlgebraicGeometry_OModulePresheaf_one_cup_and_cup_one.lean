-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_one_cup_and_cup_one
-- name    : AlgebraicGeometry.OModulePresheaf.one_cup_and_cup_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/35b31615-0e98-5ef6-b288-8e46fad919f9
-- title:
--   Unit laws for the Čech cup product
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi : V \to \operatorname{Spec} R$ a morphism. Let $F$ be an `OModulePresheaf` over $\pi$: an assignment $U \mapsto F.obj(U)$ of $R$-modules to the opens of $V$, each also a module over $\Gamma(V,U)$ compatibly with the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with $R$-linear restriction maps that are semilinear for restriction of sections and satisfy the identity and composition laws. Let $\mathcal{K}$ be an ordered affine cover of $V$: a finite linearly ordered index type with affine opens whose supremum is $\top$. For $s$ an index in degree $i$, $\mathcal{K}.inter\,s$ denotes the intersection of the corresponding opens, and a degree-$i$ cochain assigns to each such $s$ an element of $F.obj(\mathcal{K}.inter\,s)$. Write $1$ for the degree-$0$ cochain of the structure presheaf `unit π` (with $U \mapsto \Gamma(V,U)$) given by $s \mapsto 1 \in \Gamma(V,\mathcal{K}.inter\,s)$. The conclusion is the conjunction: for all $b$ and all $\beta \in F.cochain\,\mathcal{K}\,b$, the cup product $1 \cup \beta$ formed with the degree identity $0 + b = b$ equals $\beta$; and for all $a$ and all $\alpha \in (\mathrm{unit}\,\pi).cochain\,\mathcal{K}\,a$, the cup product $\alpha \cup 1$ formed with $a + 0 = a$ equals $\alpha$. The right-hand law is thus asserted for cochains valued in the structure presheaf `unit π`, not for a general $F$.
--
--   These are the two unit laws making the Čech cup product of the construction `cup` unital, with unit the constant $0$-cochain $1$. They feed into [`AlgebraicGeometry.OModulePresheaf.exists_gradedMonoid_cls_cup_unit`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_gradedMonoid_cls_cup_unit), which assembles the cup product on Čech cochains for an ordered affine cover into a graded multiplicative structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_one_cup_and_cup_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.one_cup_and_cup_one
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π)
    (𝒦 : V.OrderedAffineCover) :
    (∀ (b : ℕ) (β : F.cochain 𝒦 b),
        F.cup 𝒦 0 b b (Nat.zero_add b) (fun s => (1 : Γ(V, 𝒦.inter s))) β = β) ∧
      (∀ (a : ℕ) (α : (OModulePresheaf.unit π).cochain 𝒦 a),
        (OModulePresheaf.unit π).cup 𝒦 a 0 a (Nat.add_zero a) α (fun s => (1 : Γ(V, 𝒦.inter s))) = α) := by sorry
