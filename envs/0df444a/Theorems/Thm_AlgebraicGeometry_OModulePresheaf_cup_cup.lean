-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cup_cup
-- name    : AlgebraicGeometry.OModulePresheaf.cup_cup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/9b3f1f49-3144-5ce4-b8cc-f67ce4c7d042
-- title:
--   Associativity of the Čech cup product on cochains
-- statement:
--   Fix a commutative ring $R$, a scheme $V$ and a morphism $\pi : V \to \operatorname{Spec} R$, and let $F$ be an `OModulePresheaf` for $\pi$: an assignment $U \mapsto F.obj\,U$ of $R$-modules to the opens of $V$, each also a module over $\Gamma(V,U)$ compatibly with the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restriction maps $F.res : F.obj\,U' \to F.obj\,U$ for $U \le U'$ that are semilinear for restriction of sections, are the identity for $U = U'$ and compose. Let $\mathcal{K}$ be an ordered affine cover of $V$, i.e. a finite linearly ordered index type together with affine opens $\mathcal{K}.U\,i$ whose supremum is $\top$; for an index datum $s$ of degree $i$ write $\mathcal{K}.inter\,s = \bigwedge_j \mathcal{K}.U\,(s_j)$, and let the cochains of degree $i$ be the families $s \mapsto$ element of $F.obj(\mathcal{K}.inter\,s)$. Let $a,b,c,nab,n$ be natural numbers with $a+b = nab$ and $nab + c = n$, let $\alpha$ and $\beta$ be cochains of degrees $a$ and $b$ for the presheaf `unit` $\pi$ (namely $U \mapsto \Gamma(V,U)$ with its restriction maps), and let $\gamma$ be an $F$-cochain of degree $c$. Here the cup product of a `unit`-cochain of degree $p$ with an $F$-cochain of degree $q$, in total degree $p+q$, has value at $s$ the restriction to $\mathcal{K}.inter\,s$ of the section $\alpha$ evaluated at the front face (the first $p$ indices of $s$) acting by the $\Gamma$-module structure on $F.res$ of $\gamma$ evaluated at the back face (the last $q$ indices of $s$). The assertion is the equality of $F$-cochains of degree $n$: $(\alpha \cup \beta) \cup \gamma = \alpha \cup (\beta \cup \gamma)$, where the outer left-hand cup uses the degree witness $nab + c = n$, and on the right the inner cup is taken in degree $b+c$ and the outer one with the witness $a + (b+c) = n$.
--
--   This is the associativity of the Čech cup product at the level of cochains for an ordered affine cover, for the pairing of $\mathcal{O}$-valued cochains with $F$-valued cochains; it holds identically, before passing to cohomology. It is used in assembling the graded-monoid structure underlying the cup product with `unit`-cochains, as in [`AlgebraicGeometry.OModulePresheaf.exists_gradedMonoid_cls_cup_unit`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_gradedMonoid_cls_cup_unit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cup_cup.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.cup_cup
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π)
    (𝒦 : V.OrderedAffineCover) (a b c nab n : ℕ) (hab : a + b = nab) (hn : nab + c = n)
    (α : (OModulePresheaf.unit π).cochain 𝒦 a) (β : (OModulePresheaf.unit π).cochain 𝒦 b) (γ : F.cochain 𝒦 c) :
    F.cup 𝒦 nab c n hn ((OModulePresheaf.unit π).cup 𝒦 a b nab hab α β) γ =
      F.cup 𝒦 a (b + c) n (by omega) α (F.cup 𝒦 b c (b + c) rfl β γ) := by sorry
