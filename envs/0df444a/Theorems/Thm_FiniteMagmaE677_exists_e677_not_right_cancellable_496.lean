-- Prove2me | Theorems.Thm_FiniteMagmaE677_exists_e677_not_right_cancellable_496
-- name    : FiniteMagmaE677.exists_e677_not_right_cancellable_496
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T01:15:21.051106+00:00
-- url     : https://prove2.me/theorems/767a9009-dd8f-4f58-9111-2ec6afe85690
-- title:
--   A finite E677 magma with 496 elements that is not right-cancellative
-- statement:
--   There is a finite magma with exactly $496$ elements satisfying equation 677 which is not right-cancellative: some triple $a \neq b$ with a common third factor $c$ has $a \diamond c = b \diamond c$.
--
--   The construction is the blueprint's Chapter 13 example: the carrier is $\mathbb{Z}/31 \times \mathrm{GF}(2,4)$ with the affine base operation $3x - 2y$ and the quadratic-character fiber selection; the fifth and cube roots of unity come from a generator of the cyclic group $\mathrm{GF}(2,4)^\times$ of order $15$. Right-cancellation fails already for $(0,0)\diamond(1,0) = (0,1)\diamond(1,0)$, since the coordinate difference $1$ is a square modulo $31$ and the square fiber projects onto the second argument. The construction was verified by exhaustive search over all $496^2$ element pairs before formalization; the Lean proof is purely algebraic.
-- source:
--   Equational Theories Project, online proof blueprint, Chapter 13 (677), section 'A finite non-right-cancellative example', https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Lean instantiation contributed here.

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Definitions.Def_FiniteMagmaE677
import Definitions.Def_FiniteMagmaE677_magma496
import Theorems.Thm_FiniteMagmaE677_magma496_generic

universe u

theorem FiniteMagmaE677.exists_e677_not_right_cancellable_496 :
    ∃ (α : Type) (_ : Fintype α) (op : α → α → α),
      Nat.card α = 496 ∧ FiniteMagmaE677.E677 op ∧
      ¬(∀ a b c : α, op a c = op b c → a = b) := by sorry
