-- Prove2me | solution 1 for edenic_semiprime_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T07:29:15.175604+00:00
-- url     : https://prove2.me/submissions/4bf71f68-2755-4593-878b-ec568f1de85f

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    Squarefree n := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  exact (Nat.squarefree_mul (twin_primes_coprime p hp hp2)).mpr
    ⟨hp.squarefree, hp2.squarefree⟩
