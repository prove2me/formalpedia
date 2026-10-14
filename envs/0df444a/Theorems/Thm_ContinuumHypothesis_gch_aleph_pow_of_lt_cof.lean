-- Prove2me | Theorems.Thm_ContinuumHypothesis_gch_aleph_pow_of_lt_cof
-- name    : ContinuumHypothesis.gch_aleph_pow_of_lt_cof
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T22:34:45.904802+00:00
-- url     : https://prove2.me/theorems/b17113f6-7844-4b28-bef8-4625662f7f43
-- title:
--   GCH: $\aleph_\alpha^{\aleph_\beta}=\aleph_\alpha$ when $\beta+1<\alpha$, $\aleph_\beta<\mathrm{cf}(\aleph_\alpha)$
-- statement:
--   Assume GCH. For ordinals $\alpha,\beta$ with $\beta+1<\alpha$ and $\aleph_\beta<\mathrm{cf}(\aleph_\alpha)$ (cofinality),
--   $$\aleph_\alpha^{\aleph_\beta}=\aleph_\alpha.$$
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Implications of GCH for cardinal exponentiation', second bullet; Hayden–Kennison (1968), p. 147, exercise 76.

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem gch_aleph_pow_of_lt_cof (h : GCH.{u}) (α β : Ordinal.{u}) (hβα : β + 1 < α)
    (hcof : ℵ_ β < (ℵ_ α).ord.cof) :
    ℵ_ α ^ ℵ_ β = ℵ_ α := by sorry

end ContinuumHypothesis
