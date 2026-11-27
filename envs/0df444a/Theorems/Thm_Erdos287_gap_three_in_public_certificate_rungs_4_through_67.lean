-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_public_certificate_rungs_4_through_67
-- name    : Erdos287.gap_three_in_public_certificate_rungs_4_through_67
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T22:49:51.4164+00:00
-- url     : https://prove2.me/theorems/735862c8-5803-4640-bda3-6371165aa80f
-- title:
--   Erdős 287 public certificate rungs 4 through 67
-- statement:
--   Let $1<n_1<\cdots<n_k$ be integers whose reciprocals sum to one. The exact interval in the Lean statement consists of rungs 4 through 67 of the public Erdős #287 certificate table. If the largest denominator belongs to this interval, at least one consecutive gap is at least three.
-- source:
--   Public rung table for Erdős #287, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/data/rungs_extended.json. Compact certificate reconstruction and exact interval verification.

import Mathlib

theorem Erdos287.gap_three_in_public_certificate_rungs_4_through_67 (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 5887104692222610115311068713886416666636503914806049781997679266319785399143980188838070510421047673741709770480679026139361407216193271418506778065818374635530 < f (k - 1))
    (hhi : f (k - 1) ≤ 127121066678798445735243883196317776949351426878578394099564929136550843411572772149955019782860736757937532214437526600769419124790518099200969633104128306711796545988048739553341603835) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
