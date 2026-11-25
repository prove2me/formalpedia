-- Prove2me | Theorems.Thm_Erdos393_erdos_393_variants_luca
-- name    : Erdos393.erdos_393.variants.luca
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:43:15.04796+00:00
-- url     : https://prove2.me/theorems/fa3de3d1-1b95-55f7-8428-ad83ac5349b6
-- title:
--   variants: luca
-- statement:
--   Luca [Lu02] proved that the $abc$ conjecture implies that, for every $P \in \mathbb{Z}[x]$ of
--   degree at least $2$, the equation $P(x) = n!$ has only finitely many solutions. As remarked on
--   erdosproblems.com, this implies that $f(n) \to \infty$, conditional on the $abc$ conjecture
--   (`ABC.abc`).
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L468-L515
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L468-L515

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393
open ABC

theorem Erdos393.erdos_393.variants.luca (habc : ∀ (ε : ℝ) (hε : 0 < ε),
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ ({t.1, t.2.1, t.2.2} : Set ℕ).Pairwise Nat.Coprime ∧
    t.1 + t.2.1 = t.2.2 ∧ (radical <| t.1 * t.2.1 * t.2.2 : ℝ)^(1 + ε) < t.2.2}.Finite) : Tendsto f atTop atTop := by sorry
