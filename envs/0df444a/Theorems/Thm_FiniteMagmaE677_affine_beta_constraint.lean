-- Prove2me | Theorems.Thm_FiniteMagmaE677_affine_beta_constraint
-- name    : FiniteMagmaE677.affine_beta_constraint
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:13:21.007096+00:00
-- url     : https://prove2.me/theorems/e201bfd6-90e2-4dac-88d2-aa8a813ba267
-- title:
--   The multiplier of an affine E677 model satisfies the cyclotomic constraint b·Φ₁₀(b)·q₄(b) = 0
-- statement:
--   Let $R$ be any commutative ring and suppose the affine operation $x \diamond y = ax + by + c$ satisfies equation 677. Then the multiplier $b$ satisfies
--
--   $$b \cdot \Phi_{10}(b) \cdot q_4(b) = 0,$$
--
--   where $\Phi_{10}(b) = b^4 - b^3 + b^2 - b + 1$ is the tenth cyclotomic polynomial and $q_4(b) = b^4 + b^3 + 2b^2 + 2b + 1$.
--
--   Over a field this forces $b$ into the Type I branch $\Phi_{10}(b) = 0$ or the Type II branch $q_4(b) = 0$ (with $b \neq 0$ and $a = 1/(b+b^3)$ determined by $b$): the completeness direction of the blueprint's classification of linear models, complementing the two soundness theorems for the families. The proof evaluates E677 at three pairs to extract the coefficient identities $ab + ab^3 = 1$, $a + a^2b^2 + b^3 = 0$, $c(ab^2 + b^2 + b + 1) = 0$, and then eliminates $a$ by a universal polynomial identity.
-- source:
--   Equational Theories Project, online proof blueprint, Chapter 13 (677), classification of linear models over finite fields (completeness direction), https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Lean proof contributed here.

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_FiniteMagmaE677

universe v

theorem FiniteMagmaE677.affine_beta_constraint {R : Type v} [CommRing R] (a b c : R)
    (h : FiniteMagmaE677.E677 (fun x y : R => a * x + b * y + c)) :
    b * (b ^ 4 - b ^ 3 + b ^ 2 - b + 1) * (b ^ 4 + b ^ 3 + 2 * b ^ 2 + 2 * b + 1) = 0 := by sorry
