-- Prove2me | Theorems.Thm_ContinuumHypothesis_int_rat_equinumerous_lt_real
-- name    : ContinuumHypothesis.int_rat_equinumerous_lt_real
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T22:24:46.25298+00:00
-- url     : https://prove2.me/theorems/1f40f159-fff6-4d3a-8c83-079f42ed6151
-- title:
--   $|\mathbb Z|=|\mathbb Q|<|\mathbb R|$
-- statement:
--   The rationals can be put in one-to-one correspondence with the integers, while (Cantor) the set of integers has strictly smaller cardinality than the set of real numbers:
--   $$|\mathbb Z|=|\mathbb Q|\quad\text{and}\quad|\mathbb Z|<|\mathbb R|.$$
--
--   This is the observation that motivates the continuum hypothesis.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Cardinality of infinite sets', paragraphs 2–3.

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem int_rat_equinumerous_lt_real : #ℤ = #ℚ ∧ #ℤ < #ℝ := by sorry

end ContinuumHypothesis
