-- Prove2me | Theorems.Thm_ContinuumHypothesis_patai_gap_finite
-- name    : ContinuumHypothesis.patai_gap_finite
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T22:35:42.025005+00:00
-- url     : https://prove2.me/theorems/c6b54fda-b55d-4564-a33c-06668a33b1d9
-- title:
--   Patai: a uniform gap $2^\kappa=\kappa^{+\gamma}$ forces $\gamma<\omega$
-- statement:
--   (Patai, 1930.) Let $\gamma$ be an ordinal such that for each infinite cardinal $\kappa$, $2^\kappa$ is the $\gamma$-th successor of $\kappa$, i.e.
--   $$2^{\aleph_\alpha}=\aleph_{\alpha+\gamma}\quad\text{for every ordinal }\alpha.$$
--   Then $\gamma$ is finite.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Generalized continuum hypothesis', paragraph 4 ('László Patai proved that if γ is an ordinal and for each infinite cardinal κ, 2^κ is the γth successor of κ, then γ is finite'); Patai 1930.

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem patai_gap_finite (γ : Ordinal.{u})
    (h : ∀ α : Ordinal.{u}, (2 : Cardinal.{u}) ^ ℵ_ α = ℵ_ (α + γ)) :
    γ < Ordinal.omega0 := by sorry

end ContinuumHypothesis
