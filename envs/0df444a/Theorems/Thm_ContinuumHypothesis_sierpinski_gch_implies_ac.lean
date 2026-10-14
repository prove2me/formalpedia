-- Prove2me | Theorems.Thm_ContinuumHypothesis_sierpinski_gch_implies_ac
-- name    : ContinuumHypothesis.sierpinski_gch_implies_ac
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T22:29:52.419362+00:00
-- url     : https://prove2.me/theorems/b48d8719-01b8-47fa-af0c-2a536ebc5551
-- title:
--   Sierpiński: ZF + GCH $\vdash$ AC
-- statement:
--   (Sierpiński, 1947.) The generalized continuum hypothesis implies the axiom of choice over ZF: every model of
--   $$\mathrm{ZF}+\mathrm{GCH}$$
--   satisfies $\mathrm{AC}$. Here GCH is the choice-free form: for every infinite $S$, every $T$ with $|S|\le|T|\le|\mathcal P(S)|$ is equinumerous with $S$ or with $\mathcal P(S)$.
--
--   So there are no models of ZF in which GCH holds and AC fails.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Generalized continuum hypothesis', paragraph 3 ('Sierpiński proved that ZF + GCH implies the axiom of choice (AC)'); Gillman, Amer. Math. Monthly 109 (2002).

import Definitions.Def_CH_ZFC
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis

theorem sierpinski_gch_implies_ac : (ZF ∪ {gchSentence}) ⊨ᵇ acSentence := by sorry

end ContinuumHypothesis
