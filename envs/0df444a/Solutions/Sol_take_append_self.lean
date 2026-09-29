-- Prove2me | solution 1 for take_append_self
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-22T01:29:21.926906+00:00
-- url     : https://prove2.me/submissions/84ace271-b34b-4252-a32a-fb58002334c7

set_option autoImplicit false

theorem solution {α : Type} (l1 l2 : List α) :
    (l1 ++ l2).take l1.length = l1 := by
  rw [List.take_append]
  simp
