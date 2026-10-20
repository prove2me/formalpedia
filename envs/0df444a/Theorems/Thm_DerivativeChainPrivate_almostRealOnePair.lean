-- Prove2me | Theorems.Thm_DerivativeChainPrivate_almostRealOnePair
-- name    : DerivativeChainPrivate.almostRealOnePair
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T03:16:14.934724+00:00
-- url     : https://prove2.me/theorems/e777ad64-e63b-4baa-9acd-f2be56638578
-- title:
--   One nonreal conjugate pair: complete chain length at most two
-- statement:
--   For every n >= 1 and n unit-disk complex root slots, if their monic product has real coefficients and at most two nonreal slots counting multiplicities, there exists a complete chain through the actual iterated derivative rows with total length at most 2. This is the complete all-degree one-pair statement from the private proposal.
-- source:
--   Derivative-zero chains: public formalization reference, R39, DerivativeChainPrivate.almostRealOnePair. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.almostRealOnePair {n : ℕ} (a : Fin n → ℂ)
    (hn : 1 ≤ n) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hr : RealCoefficients a) (hc : nonrealCount a ≤ 2) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 2 := by sorry
