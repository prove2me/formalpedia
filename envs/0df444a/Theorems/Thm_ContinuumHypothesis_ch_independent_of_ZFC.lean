-- Prove2me | Theorems.Thm_ContinuumHypothesis_ch_independent_of_ZFC
-- name    : ContinuumHypothesis.ch_independent_of_ZFC
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T22:39:05.894246+00:00
-- url     : https://prove2.me/theorems/b00edd57-8d2e-460d-a3ad-b387b817bd60
-- title:
--   Independence of the continuum hypothesis from ZFC
-- statement:
--   Let $\mathrm{ZFC}$ be first-order Zermelo–Fraenkel set theory with choice and $\mathrm{CH}$ the continuum hypothesis as a sentence of set theory. If $\mathrm{ZFC}$ is consistent, then $\mathrm{ZFC}$ neither proves nor refutes $\mathrm{CH}$:
--   $$\mathrm{Con}(\mathrm{ZFC})\ \Longrightarrow\ \mathrm{ZFC}\nvdash\mathrm{CH}\ \text{ and }\ \mathrm{ZFC}\nvdash\neg\mathrm{CH}.$$
--
--   This is the resolution of Hilbert's first problem: Gödel (1940) and Cohen (1963) together.
--
--   **Formalization Note** Consistency is satisfiability and $\vdash$ is semantic consequence $\models$ (truth in every model with universe in `Type`); by Gödel's completeness theorem these agree with the syntactic notions.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; introduction ('The answer to this problem is independent of ZFC … proved in 1963 by Paul Cohen, complementing work by Kurt Gödel in 1940') and section 'Independence from ZFC'.

import Definitions.Def_CH_ZFC
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis

theorem ch_independent_of_ZFC (hZFC : ZFC.IsSatisfiable) :
    ¬ ZFC ⊨ᵇ chSentence ∧ ¬ ZFC ⊨ᵇ ∼chSentence := by sorry

end ContinuumHypothesis
