-- Prove2me | Theorems.Thm_ContinuumHypothesis_ch_iff_two_pow_aleph0_eq_aleph1
-- name    : ContinuumHypothesis.ch_iff_two_pow_aleph0_eq_aleph1
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T22:25:46.421986+00:00
-- url     : https://prove2.me/theorems/f1359f9b-c075-453d-b6c7-4a520c372af1
-- title:
--   CH $\iff 2^{\aleph_0}=\aleph_1$
-- statement:
--   Assuming the axiom of choice (as Lean does), the continuum hypothesis — no $S\subseteq\mathbb R$ has $\aleph_0<|S|<2^{\aleph_0}$ — is equivalent to
--   $$2^{\aleph_0}=\aleph_1,$$
--   where $\aleph_1$ is the least cardinal greater than $\aleph_0$.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; end of section 'Cardinality of infinite sets' ('Assuming the axiom of choice, there is a unique smallest cardinal number ℵ₁ greater than ℵ₀, and the continuum hypothesis is in turn equivalent to the equality 2^ℵ₀ = ℵ₁') and introduction.

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem ch_iff_two_pow_aleph0_eq_aleph1 : CH ↔ (2 : Cardinal.{0}) ^ ℵ₀ = ℵ_ 1 := by sorry

end ContinuumHypothesis
