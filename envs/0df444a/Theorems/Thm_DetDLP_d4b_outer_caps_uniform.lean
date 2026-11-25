-- Prove2me | Theorems.Thm_DetDLP_d4b_outer_caps_uniform
-- name    : DetDLP.d4b_outer_caps_uniform
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T09:10:00.390861+00:00
-- url     : https://prove2.me/theorems/bf375d0b-65b2-4639-9baa-6417074b8338
-- title:
--   Polynomial word cap for the outer cursor
-- statement:
--   A uniform polynomial cap covers every controller state, tagged query, scalar reply, prefix accumulator, and possible header buffer on a supplied enumerated binary plan.
-- source:
--   Resource accounting for outer scalar cursor dc44082d-fc56-402c-8efa-dc7eda4aebd8.

import Definitions.Def_DetDLP_D4BOuterInvariant
set_option autoImplicit false
open DetDLP DetDLP.D4BOuter DetDLP.D4Plan DetDLP.D4BEntry DetDLP.ResidualScalarOracle OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4b_outer_caps_uniform (C c e : ℕ) : ∃ k : ℕ, ∀ (x : Input C c) (P : Plan x) {A o}, Enumerates A o e P → ∀ v : DigitsData P,
    (∀ u a i, v u a i < 2 ^ precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)) →
    let H := np k (size x)
    (pair (input x) []).length ≤ H ∧ (answer x).length ≤ H ∧
    (∀ b : D4BOuter.Bits, b.length ≤ 2*need P+1 → (pair (hdState x b) (tagWord 1 (rankQuery x 0))).length ≤ H ∧ (pair (hdState x b) (header P)).length ≤ H) ∧
    (∀ u s, (pair (brState P u s) (tagWord 1 (rankQuery x (u.val+1)))).length ≤ H ∧ (pair (brState P u s) (branch P u)).length ≤ H) ∧
    (∀ u a s t, (pair (dgState P u a s t) (tagWord 2 (dgQuery P u a))).length ≤ H ∧ (pair (dgState P u a s t) (dgAns P v u a)).length ≤ H) ∧ need P ≤ H := by sorry
