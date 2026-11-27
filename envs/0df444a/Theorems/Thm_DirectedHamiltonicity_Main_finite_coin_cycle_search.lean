-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_finite_coin_cycle_search
-- name    : DirectedHamiltonicity.Main.finite_coin_cycle_search
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:09:30.696918+00:00
-- url     : https://prove2.me/theorems/801c7078-a678-5884-ae05-cb3cd71a722b
-- title:
--   A one-sided finite-coin search for directed Hamiltonian cycles using weighted parity
-- statement:
--   There is a fixed bounded log-cost RAM for the weighted parity calls in the explicit finite-tape edge-deletion algorithm. The complete search gives the specified answer on graphs of size zero or one, never accepts a graph without a Hamiltonian cycle on any tape, and succeeds on every yes graph with probability at least two thirds at every sufficiently long uniform tape length. All randomness and candidate query encodings are specified.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, Section 2, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_DirectedHamiltonicity_CycleSearch

open TargetedSamplers DirectedHamiltonicity.Main DirectedHamiltonicity.Main.CycleReduction

theorem DirectedHamiltonicity.Main.finite_coin_cycle_search : ∃ (Q : Program) (A k : ℕ), QueryTime Q A k ∧
    ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
      (n≤1 → ∀ c, answer Q A k adj c = smallCycleAnswer n adj) ∧
      (∀ c, answer Q A k adj c = true → HasHamCycle n adj) ∧
      (HasHamCycle n adj → ∀ L : ℕ, coinCount n (coinSpan A k n) ≤ L →
        (2/3:ℝ) ≤ acceptsFraction (answer Q A k adj) L) := by sorry
