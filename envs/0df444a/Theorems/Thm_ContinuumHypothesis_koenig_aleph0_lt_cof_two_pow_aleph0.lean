-- Prove2me | Theorems.Thm_ContinuumHypothesis_koenig_aleph0_lt_cof_two_pow_aleph0
-- name    : ContinuumHypothesis.koenig_aleph0_lt_cof_two_pow_aleph0
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T22:29:33.531639+00:00
-- url     : https://prove2.me/theorems/a5640125-8678-4800-8f26-3c4a453f0e00
-- title:
--   Kőnig: $\mathrm{cf}(2^{\aleph_0})>\aleph_0$
-- statement:
--   The cardinality of the continuum does not have cofinality $\omega$:
--   $$\mathrm{cf}\big(2^{\aleph_0}\big)>\aleph_0 .$$
--   So $2^{\aleph_0}$ cannot be $\aleph_\omega$, $\aleph_{\omega_1+\omega}$, or any cardinal of cofinality $\omega$.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Independence from ZFC', paragraph 4 ('per Kőnig's theorem, it is not consistent to assume 2^ℵ₀ is ℵ_ω or ℵ_{ω₁+ω} or any cardinal with cofinality ω').

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem koenig_aleph0_lt_cof_two_pow_aleph0 : ℵ₀ < ((2 : Cardinal.{0}) ^ ℵ₀).ord.cof := by sorry

end ContinuumHypothesis
