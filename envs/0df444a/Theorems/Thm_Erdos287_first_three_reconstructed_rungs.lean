-- Prove2me | Theorems.Thm_Erdos287_first_three_reconstructed_rungs
-- name    : Erdos287.first_three_reconstructed_rungs
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:07:50.653238+00:00
-- url     : https://prove2.me/theorems/7ac89013-ce14-5a38-af4d-85f3abd930f8
-- title:
--   Erdős 287 for the first three reconstructed prime certificate intervals
-- statement:
--   For a representation of 1 by reciprocals of increasing integer denominators greater than 1, some consecutive gap is at least three if the maximum is in the stated interval (just above 3.81185×10^158 through about 5.88710×10^159).
-- source:
--   Erdős Problem #287. Independently reconstructed and Lean-checked from rows 0–2 of Zed-Rez/erdos-287-lean data/rungs_extended.json at 2b2ecb1022cc3bfe249d9733003d3488f2d3027f.

import Mathlib

theorem Erdos287.first_three_reconstructed_rungs (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325436 ≤ f (k - 1))
    (hhi : f (k - 1) ≤ 5887104692222610115311068713886416666636503914806049781997679266319785399143980188838070510421047673741709770480679026139361407216193271418506778065818374635530) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
