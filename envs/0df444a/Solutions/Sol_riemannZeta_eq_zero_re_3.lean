-- Prove2me | solution 3 for riemannZeta_eq_zero_re
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @LG
-- created : 2026-11-21T16:23:14.48161+00:00
-- url     : https://prove2.me/submissions/2abfb056-5adf-4169-9673-4d464f9f1a5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GRH_riemannZeta_zero_nontrivial_in_critical_strip
import Theorems.Thm_AlpoegeClaudeRH_EveryCharacter
import Theorems.Thm_AlpoegeClaudeRH_RH_from_EveryCharacter

theorem solution : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2 := by
  intro s hz htriv hs1
  have hstrip := GRH.riemannZeta_zero_nontrivial_in_critical_strip hz htriv
  exact AlpoegeClaudeRH.RH_from_EveryCharacter AlpoegeClaudeRH.EveryCharacter s hstrip.1 hstrip.2 hz
