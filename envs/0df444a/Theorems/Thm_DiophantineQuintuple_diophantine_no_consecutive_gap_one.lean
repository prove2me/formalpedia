-- Prove2me | Theorems.Thm_DiophantineQuintuple_diophantine_no_consecutive_gap_one
-- name    : DiophantineQuintuple.diophantine_no_consecutive_gap_one
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-28T01:34:08.983823+00:00
-- url     : https://prove2.me/theorems/0b1439fb-5062-4261-bf1c-d732cf786be4
-- title:
--   Gap-one exclusion: no ordered Diophantine quintuple starts with a one-gap
-- statement:
--   Let f : Fin 5 → Nat be a Diophantine quintuple (Quintuple f) with strictly increasing entries (Ordered f). Then f 1 - f 0 = 1 is impossible: the two smallest consecutive entries of a Diophantine quintuple cannot be at distance 1. The proof is elementary (between-squares): the Diophantine-pair property of f at entries (0,1) gives r with f 0 * f 1 + 1 = r^2; with f 1 = f 0 + 1 this yields f 0^2 < r^2 < (f 0 + 1)^2, forcing f 0 < r < f 0 + 1, impossible for a natural number r. This is the elementary fragment of the Cipu–Fujita gap classification: together with the gap-two exclusion fujita_gap_two_no_quintuple (deep input, Fujita 2008, transcendence method) it yields f 1 - f 0 >= 3 for any ordered Diophantine quintuple, which is the remaining input behind diophantine_no_consecutive_gap_two.
-- source:
--   Elementary between-squares argument (folk). Deep sibling: Y. Fujita, "The extensibility of Diophantine pairs {k-1,k+1}", J. Number Theory 128 (2008), 322-353.

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem DiophantineQuintuple.diophantine_no_consecutive_gap_one (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) (h1 : f 1 - f 0 = 1) : False := by sorry
