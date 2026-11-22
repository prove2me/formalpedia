-- Prove2me | solution 1 for sqrt5_bounds
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T10:42:27.25244+00:00
-- url     : https://prove2.me/submissions/b053ef7f-276b-4ec8-b6dd-a561035285aa

theorem solution : 2236^2 < 5 * 1000^2 ∧ 5 * 1000^2 < 2238^2 := by
  constructor
  · decide
  · decide