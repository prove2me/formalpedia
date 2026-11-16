-- Prove2me | Theorems.Thm_CNFEncComplexity_uniformNativeExpander
-- name    : CNFEncComplexity.uniformNativeExpander
-- status  : Proved
-- author  : @bersubs
-- created : 2026-11-15T06:55:16.936915+00:00
-- url     : https://prove2.me/theorems/ffbeed1d-5915-48f0-b12a-c3a2cefa2af8
-- title:
--   Uniform explicit expander with a binary multitape certificate
-- statement:
--   A single polynomial-time neighbor function supplies Teutsch’s bounded-degree Hall expanders for all valid universe sizes and thresholds. The machine certificate uses the binary multitape representation needed for composition.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614, Lemma 11, Section 3.4.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Option
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Union
import Mathlib.Data.Nat.Log

open Turing.MultiTapeTM

theorem CNFEncComplexity.uniformNativeExpander :
    ∃ c : ℕ, ∃ nbr : ℕ × ℕ × ℕ × ℕ → Option ℕ,
      ComputableTidilyInPolyTime nbr (encPair encNat (encPair encNat (encPair encNat encNat))) (encOption encNat) ∧
      ∀ k N : ℕ, 2 ^ k ≤ N → ∃ r : ℕ, r < 2 ^ (k + 3) ∧
        (∀ l < N, ∀ i : ℕ, c * (Nat.log 2 N + 1) ^ c ≤ i → nbr (N, k, l, i) = none) ∧
        (∀ l < N, ∀ i ρ : ℕ, nbr (N, k, l, i) = some ρ → ρ < r) ∧
        ∀ S : Finset (Fin N), S.card ≤ 2 ^ k →
          S.card ≤ (S.biUnion fun l => (Finset.range (c * (Nat.log 2 N + 1) ^ c)).biUnion
            fun i => (nbr (N, k, (l : ℕ), i)).toFinset).card := by sorry
