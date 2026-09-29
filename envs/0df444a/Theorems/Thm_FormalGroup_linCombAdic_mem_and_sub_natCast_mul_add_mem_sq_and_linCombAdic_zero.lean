-- Prove2me | Theorems.Thm_FormalGroup_linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero
-- name    : FormalGroup.linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/f24322f5-f4fc-5596-9b14-247629b7e4a4
-- title:
--   Adic formal linear combinations modulo I and I²
-- statement:
--   Let $R$ be a commutative ring and $I \subseteq R$ an ideal for which $R$ is $I$-adically complete, let $F$ be a one-dimensional formal group law over $R$ (a term of the project's structure `FormalGroup R`), and let $x_0, x_1 \in I$ and $a, b \in \mathbb{N}$. Here $F$ provides evaluation operations $F.\mathrm{eval}$ and $F.\mathrm{evalNSMul}$ on a topologised base, and [`FormalGroup.linComb F x₀ x₁ a b`](def/FormalGroup_DrinfeldBasis.html#L12) is by definition $F.\mathrm{eval}\bigl(F.\mathrm{evalNSMul}\,a\,x_0,\ F.\mathrm{evalNSMul}\,b\,x_1\bigr)$, the value $[a]_F x_0 +_F [b]_F x_1$; [`FormalGroup.linCombAdic F I x₀ x₁ a b`](def/FormalGroup_DrinfeldBasis.html#L38) is this same quantity formed with the $I$-adic structure on $R$ supplied by $I$. The theorem asserts the conjunction of three things: first, $F.\mathrm{linCombAdic}\,I\,x_0\,x_1\,a\,b \in I$; second, $F.\mathrm{linCombAdic}\,I\,x_0\,x_1\,a\,b - (a\,x_0 + b\,x_1) \in I^2$, where $a$ and $b$ act through their images in $R$; and third, the value at $a = b = 0$ vanishes, $F.\mathrm{linCombAdic}\,I\,x_0\,x_1\,0\,0 = 0$ (so this last clause is independent of the given $a$ and $b$).
--
--   These are the basic size estimates for the formal points $[a]_F x_0 +_F [b]_F x_1$ attached to a pair of $I$-adically small points of a formal group law: they are again $I$-adically small, and to first order they are the linear forms $a x_0 + b x_1$. They are used in the analysis of Drinfeld bases on the formal chart at a supersingular point, and in the computations of the action of level structures on origin parameters for modular curves that cite this result.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing FormalGroup

theorem FormalGroup.linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero
    (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (F : FormalGroup R)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (a b : ℕ) :
    F.linCombAdic I x₀ x₁ a b ∈ I ∧
      F.linCombAdic I x₀ x₁ a b - ((a : R) * x₀ + (b : R) * x₁) ∈ I ^ 2 ∧
      F.linCombAdic I x₀ x₁ 0 0 = 0 := by sorry
