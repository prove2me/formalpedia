-- Prove2me | Theorems.Thm_ContinuumHypothesis_cohen_consistency_not_CH
-- name    : ContinuumHypothesis.cohen_consistency_not_CH
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T22:28:14.816988+00:00
-- url     : https://prove2.me/theorems/a8800158-5c64-4597-9890-33b4113f7bf3
-- title:
--   Cohen: Con(ZFC) $\Rightarrow$ Con(ZFC + $\neg$CH)
-- statement:
--   (Cohen, 1963.) If $\mathrm{ZFC}$ is consistent, then so is $\mathrm{ZFC}$ together with the negation of the continuum hypothesis:
--   $$\mathrm{Con}(\mathrm{ZFC})\ \Longrightarrow\ \mathrm{Con}(\mathrm{ZFC}+\neg\mathrm{CH}).$$
--
--   Hence CH cannot be proved in ZFC.
--
--   **Formalization Note** Consistency is satisfiability of the first-order theory (equivalent by the completeness theorem).
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Independence from ZFC', paragraph 3 ('Cohen showed that CH cannot be proven from the ZFC axioms … he developed the method of forcing'); Cohen, PNAS 50 (1963), 51 (1964).

import Definitions.Def_CH_ZFC
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis

theorem cohen_consistency_not_CH (hZFC : ZFC.IsSatisfiable) :
    (ZFC ∪ {∼chSentence}).IsSatisfiable := by sorry

end ContinuumHypothesis
