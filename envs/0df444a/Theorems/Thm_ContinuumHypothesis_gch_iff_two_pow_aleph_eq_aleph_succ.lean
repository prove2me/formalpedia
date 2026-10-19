-- Prove2me | Theorems.Thm_ContinuumHypothesis_gch_iff_two_pow_aleph_eq_aleph_succ
-- name    : ContinuumHypothesis.gch_iff_two_pow_aleph_eq_aleph_succ
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T22:30:26.736946+00:00
-- url     : https://prove2.me/theorems/f5a09bda-9be5-46ec-b39e-84d83919c30e
-- title:
--   GCH $\iff 2^{\aleph_\alpha}=\aleph_{\alpha+1}$ for all $\alpha$
-- statement:
--   (Cantor's aleph hypothesis.) The generalized continuum hypothesis — no infinite cardinal $\kappa$ has a cardinal strictly between $\kappa$ and $2^\kappa$ — is equivalent to
--   $$2^{\aleph_\alpha}=\aleph_{\alpha+1}\quad\text{for every ordinal }\alpha.$$
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Generalized continuum hypothesis', paragraph 1 ('GCH is equivalent to: ℵ_{α+1} = 2^{ℵ_α} for every ordinal α').

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem gch_iff_two_pow_aleph_eq_aleph_succ :
    GCH.{u} ↔ ∀ α : Ordinal.{u}, (2 : Cardinal.{u}) ^ ℵ_ α = ℵ_ (α + 1) := by sorry

end ContinuumHypothesis
