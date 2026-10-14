-- Prove2me | Theorems.Thm_ContinuumHypothesis_gch_iff_aleph_eq_beth
-- name    : ContinuumHypothesis.gch_iff_aleph_eq_beth
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T22:33:33.657981+00:00
-- url     : https://prove2.me/theorems/b497bfb9-406d-450e-9764-28bd2e243dc7
-- title:
--   GCH $\iff \aleph_\alpha=\beth_\alpha$ for all $\alpha$
-- statement:
--   In terms of the beth numbers ($\beth_0=\aleph_0$, $\beth_{\alpha+1}=2^{\beth_\alpha}$, $\beth_\lambda=\sup_{\alpha<\lambda}\beth_\alpha$ at limits), the generalized continuum hypothesis is equivalent to
--   $$\aleph_\alpha=\beth_\alpha\quad\text{for every ordinal }\alpha.$$
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Generalized continuum hypothesis', paragraph 2 ('The beth numbers provide an alternative notation for this condition: ℵ_α = ℶ_α for every ordinal α').

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem gch_iff_aleph_eq_beth : GCH.{u} ↔ ∀ α : Ordinal.{u}, ℵ_ α = ℶ_ α := by sorry

end ContinuumHypothesis
