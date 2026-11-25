-- Prove2me | solution 1 for edenic_semiprime_first_examples
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T06:23:04.111888+00:00
-- url     : https://prove2.me/submissions/23539d5e-0211-4b9b-b4a3-1aa15017b48b

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution :
    IsEdenicSemiprime 15 ∧ IsEdenicSemiprime 35 ∧ IsEdenicSemiprime 143 ∧
      IsEdenicSemiprime 323 := by
  refine ⟨⟨3, by decide, by decide, rfl⟩, ⟨5, by decide, by decide, rfl⟩,
    ⟨11, by decide, by decide, rfl⟩, ⟨17, by decide, by decide, rfl⟩⟩
