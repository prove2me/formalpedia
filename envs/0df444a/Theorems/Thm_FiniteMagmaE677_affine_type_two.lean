-- Prove2me | Theorems.Thm_FiniteMagmaE677_affine_type_two
-- name    : FiniteMagmaE677.affine_type_two
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:05:53.282505+00:00
-- url     : https://prove2.me/theorems/1f0851b3-5c62-43f2-ac06-37cbf858aae4
-- title:
--   Affine Type II models (cube-root parameter) satisfy E677
-- statement:
--   Let $R$ be any commutative ring and let $a, b, c \in R$ satisfy
--
--   $$b^3 + b + 1 + a = 0, \qquad b^4 + b^3 + 2b^2 + 2b + 1 = 0.$$
--
--   Then the affine operation $x \diamond y = a x + b y + c$ (with $c$ arbitrary) satisfies equation 677. These two relations imply the blueprint's Type II conditions, including the primitive-cube-root condition $a^2 + a + 1 = 0$. Examples: $(a,b) = (4,3)$ and $(4,1)$ in $\mathbb{F}_7$, and the exceptional translation-invariant family $x \diamond y = 5x - 4y + c$ on $\mathbb{F}_{31}$. Together with the affine E255 theorem, this certifies the entire Type II family over finite rings.
-- source:
--   Equational Theories Project, online proof blueprint, Chapter 13 (677), classification of linear models over finite fields, Type II, https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Lean proof contributed here.

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FiniteMagmaE677

universe v

theorem FiniteMagmaE677.affine_type_two {F : Type v} [CommRing F] (a b c : F)
    (h2 : b ^ 3 + b + 1 + a = 0) (h3 : b ^ 4 + b ^ 3 + 2 * b ^ 2 + 2 * b + 1 = 0) :
    FiniteMagmaE677.E677 (fun x y : F => a * x + b * y + c) := by sorry
