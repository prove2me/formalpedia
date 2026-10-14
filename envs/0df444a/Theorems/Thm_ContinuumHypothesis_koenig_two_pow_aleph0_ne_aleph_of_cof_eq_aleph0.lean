-- Prove2me | Theorems.Thm_ContinuumHypothesis_koenig_two_pow_aleph0_ne_aleph_of_cof_eq_aleph0
-- name    : ContinuumHypothesis.koenig_two_pow_aleph0_ne_aleph_of_cof_eq_aleph0
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T22:29:03.133635+00:00
-- url     : https://prove2.me/theorems/233c5876-ce8d-48f6-8cb6-d5bfd5fe6037
-- title:
--   Kőnig: $2^{\aleph_0}\neq\aleph_\alpha$ when $\mathrm{cf}(\alpha)=\omega$
-- statement:
--   (Kőnig, 1906; with Hausdorff's notion of cofinality.) For every ordinal $\alpha$ of cofinality $\omega$,
--   $$2^{\aleph_0}\neq\aleph_\alpha.$$
--   For example $2^{\aleph_0}\neq\aleph_\omega$.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'History', paragraph 4 ('Kőnig's theorem … shows that 2^ℵ₀ cannot equal ℵ_α for α with cofinality ω. For example, 2^ℵ₀ ≠ ℵ_ω').

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem koenig_two_pow_aleph0_ne_aleph_of_cof_eq_aleph0 (α : Ordinal.{0}) (hα : α.cof = ℵ₀) :
    (2 : Cardinal.{0}) ^ ℵ₀ ≠ ℵ_ α := by sorry

end ContinuumHypothesis
