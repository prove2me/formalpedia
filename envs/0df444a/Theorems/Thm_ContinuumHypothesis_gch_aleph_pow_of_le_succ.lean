-- Prove2me | Theorems.Thm_ContinuumHypothesis_gch_aleph_pow_of_le_succ
-- name    : ContinuumHypothesis.gch_aleph_pow_of_le_succ
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T22:34:26.155276+00:00
-- url     : https://prove2.me/theorems/e0e319da-e32c-497d-867c-441cf3504c5c
-- title:
--   GCH: $\aleph_\alpha^{\aleph_\beta}=\aleph_{\beta+1}$ when $\alpha\le\beta+1$
-- statement:
--   Assume GCH. For ordinals $\alpha,\beta$ with $\alpha\le\beta+1$,
--   $$\aleph_\alpha^{\aleph_\beta}=\aleph_{\beta+1}.$$
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Implications of GCH for cardinal exponentiation', first bullet; Hayden–Kennison, Zermelo-Fraenkel Set Theory (1968), p. 147, exercise 76.

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem gch_aleph_pow_of_le_succ (h : GCH.{u}) (α β : Ordinal.{u}) (hαβ : α ≤ β + 1) :
    ℵ_ α ^ ℵ_ β = ℵ_ (β + 1) := by sorry

end ContinuumHypothesis
