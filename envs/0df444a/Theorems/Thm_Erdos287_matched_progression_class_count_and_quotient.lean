-- Prove2me | Theorems.Thm_Erdos287_matched_progression_class_count_and_quotient
-- name    : Erdos287.matched_progression_class_count_and_quotient
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T15:43:06.776305+00:00
-- url     : https://prove2.me/theorems/0529e9ff-e111-56cb-9b59-838017309d8e
-- title:
--   Matched residue class count and frozen quotient
-- statement:
--   For positive $b$, exactly $q$ representatives modulo $bq$ lie in a given class modulo $b$. If $p-x=bs$ and $p-x'=bs'$, then $x\equiv x'\pmod{bq}$ implies $s\equiv s'\pmod q$.
-- source:
--   Erdős #287 Type II dispersion audit.

import Mathlib

theorem Erdos287.matched_progression_class_count_and_quotient (b q n : ℕ) (hb : 0 < b) :
    ((Finset.range (b * q)).filter (fun a => a ≡ n [MOD b])).card = q ∧
    ∀ (p x x' s s' : ℤ), p - x = (b : ℤ) * s → p - x' = (b : ℤ) * s' →
      x ≡ x' [ZMOD (b : ℤ) * q] → s ≡ s' [ZMOD q] := by sorry
