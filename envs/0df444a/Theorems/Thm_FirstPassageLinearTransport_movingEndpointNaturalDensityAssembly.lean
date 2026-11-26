-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_movingEndpointNaturalDensityAssembly
-- name    : FirstPassageLinearTransport.movingEndpointNaturalDensityAssembly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:38:06.972435+00:00
-- url     : https://prove2.me/theorems/6c52769e-8620-4553-b8ba-713f92364064
-- title:
--   First Passage Linear Transport: moving Endpoint Natural Density Assembly
-- statement:
--   Assemble a moving shell profile after its literal density and witness
--   estimates have been proved.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointAssembly.lean#L27-L60
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointAssembly.lean#L27-L60

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAssembly
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.movingEndpointNaturalDensityAssembly
    (S : ℕ → Set ℕ) {A : ℕ → ℝ} {c beta C eps : ℝ}
    (heps : 0 < eps)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hShell : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (S M) M ≤
        C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps))))
    (hWitness : ∀ᶠ M : ℕ in atTop,
      ∀ n : ℕ, n ∈ dyadicShell M → n ∈ S M →
        ∃ k : ℕ,
          (k : ℝ) < c * Real.log n ∧
          (orbit k n : ℝ) < C * (Real.log n) ^ (A M) ∧
          ∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)) :
    NaturalDensityOne (assembleDyadic S) ∧
      ∀ᶠ n : ℕ in atTop,
        n ∈ assembleDyadic S →
          ∃ k : ℕ,
            (k : ℝ) < c * Real.log n ∧
            (orbit k n : ℝ) <
              C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
            ∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by sorry
