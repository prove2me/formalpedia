-- Prove2me | Theorems.Thm_ContinuumHypothesis_goedel_consistency_AC_GCH
-- name    : ContinuumHypothesis.goedel_consistency_AC_GCH
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T22:26:22.378473+00:00
-- url     : https://prove2.me/theorems/86e24aa2-bd1f-4742-ac30-7f6ce0d56529
-- title:
--   Gödel: Con(ZF) $\Rightarrow$ Con(ZFC + GCH)
-- statement:
--   (Gödel, 1938/1940.) If $\mathrm{ZF}$ is consistent, then so is $\mathrm{ZF}$ together with the axiom of choice and the generalized continuum hypothesis:
--   $$\mathrm{Con}(\mathrm{ZF})\ \Longrightarrow\ \mathrm{Con}(\mathrm{ZFC}+\mathrm{GCH}).$$
--
--   In particular CH (a consequence of GCH) cannot be disproved in ZFC.
--
--   **Formalization Note** Consistency is satisfiability of the first-order theory (equivalent by the completeness theorem).
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Independence from ZFC', paragraph 2 ('His proof shows that both CH and AC hold in the constructible universe L') and section 'Generalized continuum hypothesis' ('Kurt Gödel showed that GCH is a consequence of ZF + V=L … and is therefore consistent with ZFC'); Gödel 1938, 1940.

import Definitions.Def_CH_ZFC
open FirstOrder FirstOrder.Language

namespace ContinuumHypothesis

theorem goedel_consistency_AC_GCH (hZF : ZF.IsSatisfiable) :
    (ZFC ∪ {gchSentence}).IsSatisfiable := by sorry

end ContinuumHypothesis
