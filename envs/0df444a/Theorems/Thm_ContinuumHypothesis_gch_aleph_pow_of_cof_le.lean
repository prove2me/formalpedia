-- Prove2me | Theorems.Thm_ContinuumHypothesis_gch_aleph_pow_of_cof_le
-- name    : ContinuumHypothesis.gch_aleph_pow_of_cof_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T22:35:24.448041+00:00
-- url     : https://prove2.me/theorems/9f79f942-dd79-41ed-b073-7a7e7b90f6be
-- title:
--   GCH: $\aleph_\alpha^{\aleph_\beta}=\aleph_{\alpha+1}$ when $\beta+1<\alpha$, $\mathrm{cf}(\aleph_\alpha)\le\aleph_\beta$
-- statement:
--   Assume GCH. For ordinals $\alpha,\beta$ with $\beta+1<\alpha$ and $\aleph_\beta\ge\mathrm{cf}(\aleph_\alpha)$,
--   $$\aleph_\alpha^{\aleph_\beta}=\aleph_{\alpha+1}.$$
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Implications of GCH for cardinal exponentiation', third bullet; Hayden–Kennison (1968), p. 147, exercise 76.

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem gch_aleph_pow_of_cof_le (h : GCH.{u}) (α β : Ordinal.{u}) (hβα : β + 1 < α)
    (hcof : (ℵ_ α).ord.cof ≤ ℵ_ β) :
    ℵ_ α ^ ℵ_ β = ℵ_ (α + 1) := by sorry

end ContinuumHypothesis
