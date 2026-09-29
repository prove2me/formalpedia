-- Prove2me | Theorems.Thm_BlockCycleRotation_muCost_homogeneous
-- name    : BlockCycleRotation.muCost_homogeneous
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:06:14.057066+00:00
-- url     : https://prove2.me/theorems/2762f421-b391-455b-a689-ba20a8f6d9a3
-- title:
--   Corollary, item 2: homogeneity
-- statement:
--   **Corollary, item 2: homogeneity.** `μ(λN, λℓ, λβ) = λ·μ(N,ℓ,β)`.
--
--   In Blomer–Bux this is **Corollary 6(2)**, “Corollary 6(2): `μ(λN,λℓ,λβ) = λμ(N,ℓ,β)`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Corollary 6(2). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L462-L471

import Definitions.Def_BlockCycleRotation_Buffer
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.muCost_homogeneous {lam N l b : ℝ} (hlam : 0 < lam) (hN : 0 < N) :
    muCost (lam * N) (lam * l) (lam * b) = lam * muCost N l b := by sorry
