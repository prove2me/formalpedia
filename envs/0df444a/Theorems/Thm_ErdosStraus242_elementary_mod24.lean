-- Prove2me | Theorems.Thm_ErdosStraus242_elementary_mod24
-- name    : ErdosStraus242.elementary_mod24
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:42:41.451946+00:00
-- url     : https://prove2.me/theorems/dcb2fea7-49da-4929-8742-019781b318fd
-- title:
--   All inputs outside one modulo twenty-four
-- statement:
--   For every natural number $n>2$ with $n\not\equiv1\pmod{24}$, there exist natural numbers $1≤ x<y<z$ such that $4/n=1/x+1/y+1/z$ in the rationals. Primality of $n$ is not required.
-- source:
--   Locally proved consequence of the even family and elementary families A–D; compare the elementary congruences in Bloom–Elsholtz (2022), p. 239, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem elementary_mod24 (n : ℕ) (hn : 2 < n) (hmod : n % 24 ≠ 1) :
    IsErdosStraus n := by sorry
end ErdosStraus242
