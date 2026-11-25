-- Prove2me | Theorems.Thm_DetDLP_d4_active_node_preconditions
-- name    : DetDLP.d4_active_node_preconditions
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T08:28:38.037806+00:00
-- url     : https://prove2.me/theorems/b163faa0-fe23-4901-abdd-ff4c376a1761
-- title:
--   Local numerical preconditions and successor invariants for the active partial unroll
-- statement:
--   At any active depth, the width fits the shift and the mass; the residue grid, label padding and degree potential fit the available resources. The child precision is at most 64 times the mass times the tile scale divided by the width; the next absolute-depth precision and degree obey the stopped-schedule invariants. This is the quantitative active-node argument in the proof of Lemma 5.3(i), independent of the host and the choice of modulus.

import Definitions.Def_DetDLP_D4Plan
import Definitions.Def_DetDLP_D3StoppedSchedule
set_option autoImplicit false
open DetDLP DetDLP.D4Plan DetDLP.D3Stopped DetDLP.AppendixD4

theorem DetDLP.d4_active_node_preconditions (C : ℕ) (hC : 0 < C) : ∃ L₀ : ℕ, ∀ {c : ℕ} (x : Input C c) (d M Δ p : ℕ),
    L₀ ≤ D3Stopped.level x.S → D3Stopped.threshold x.S < M → M ≤ x.S / 8^d →
    let a := shift x.S d; let u := width x.S d; let last := if d=0 then 0 else shift x.S (d-1)
    Δ ≤ max (C * Nat.ceil ((x.b:ℝ)^((3:ℝ)/4))) (2*2^last) →
    p ≤ x.p+80*x.S*2^last →
    1 ≤ u ∧ u ≤ a ∧ u ≤ M ∧ 1 ≤ x.l ∧ points M a ≤ 2^(4*D3Stopped.level x.S) ∧
    2^a*64^(2*a) ≤ M ∧ (a+2)*64^(4*a)*max 1 Δ ≤ M ∧ max Δ (2*2^a) ≤ cap x.S ∧
    (∀ i < u, p+increase M a u i ≤ 64*M*tileScale a i/u) ∧
    ∀ i, p+increase M a u i ≤ x.p+80*x.S*2^a := by sorry
