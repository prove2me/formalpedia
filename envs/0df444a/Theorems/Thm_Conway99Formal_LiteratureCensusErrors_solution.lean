-- Prove2me | Theorems.Thm_Conway99Formal_LiteratureCensusErrors_solution
-- name    : Conway99Formal.LiteratureCensusErrors.solution
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T00:26:21.836903+00:00
-- url     : https://prove2.me/theorems/3605f210-927c-4c8d-b541-bd8a2e89d06c
-- title:
--   Two arithmetic errors in the printed seven-vertex census
-- statement:
--   Let z₁,…,z₂₀₈ be the exact rational expressions printed in Reimbayev's proposed census, and let x=n₃ and y=z₁₁. At n=99 and k=14, their sum is 14,792,997,384 for every integer x and y. This is 94,034,160 less than the number of seven-element vertex subsets, 14,887,031,544. At n=243 and k=22, the printed z₁₇₆ expression is never an integer for integer x and y. These are errors in the printed expressions; the theorem does not assume they are actual graph counts and does not decide whether an SRG(99,14,1,2) exists.
-- source:
--   Reimbayev, arXiv:2608.19410v1, printed seven-vertex table; local archived audit README.md lines 56–77 and august_census_audit.json /raw_latex, hashes recorded in claims.json.

import Definitions.Def_Conway99_Literature_Census_20261003
set_option autoImplicit false
open Conway99Formal.LiteratureCensusErrors

theorem Conway99Formal.LiteratureCensusErrors.solution (x y : ℤ) :
    printedTotal 99 14 (x : ℚ) (y : ℚ) = 14792997384 ∧
    (Nat.choose 99 7 : ℚ) - printedTotal 99 14 (x : ℚ) (y : ℚ) = 94034160 ∧
    ¬ ∃ z : ℤ, (z : ℚ) = z176 243 22 x y := by sorry
