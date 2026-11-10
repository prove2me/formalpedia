-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_minimally_dependent_reduction
-- name    : ApproxPolySatCH.Main.minimally_dependent_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:12:56.486546+00:00
-- url     : https://prove2.me/theorems/e232928e-0543-4661-8335-5a3e253638df
-- title:
--   Proposition 3 — Reduction to minimal dependence
-- statement:
--   There is one randomized polynomial-time bit algorithm taking a sparse polynomial system over a rational or explicitly described finite coefficient field to a minimally dependent tuple. With probability at least $2/3$, the output is a valid tuple of $m+1$ polynomials in $m\ge1$ variables and has the same APS status:
--   $$\mathrm{APS}(f)\iff\mathrm{APS}(g).$$
--   Over the rationals all output coefficients remain rational. Over a finite field the output uses a specified finite extension, with an actual embedding and extension degree bounded by a polynomial in the total binary input length. One finite machine, time bound, seed-length polynomial and extension bound work before all inputs, including the field description.
--
--   This is the preprocessing reduction used before the prescribed-fiber argument.
--
--   Differences from the source:
--   - generalization: The reduction is stated for APS over a fixed rational or finite coefficient field. → One machine also accepts the explicitly supplied coefficient-field presentation.; reason: The field operations and randomized extension construction in §3 are uniform and their bit costs are included in the same input-length clock.
--   - encoding: A randomized polynomial-time reduction with polynomial-degree finite extensions. → A finite transition table, global polynomial clock and seed length, success count at least two thirds, and written output with an actual field embedding.; reason: This fixes the conventional error at at most one third, charges field and output work, and includes the source’s constant-system preprocessing.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Proposition 3, p.16 (PDF p.16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=16

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem minimally_dependent_reduction : MinimalReduction := by sorry

end ApproxPolySatCH.Main
