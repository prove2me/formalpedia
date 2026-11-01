-- Prove2me | Theorems.Thm_AndOrSched_section_1_redundant_or_arcs
-- name    : AndOrSched.section_1_redundant_or_arcs
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:37.828972+00:00
-- url     : https://prove2.me/theorems/0db51859-ed9d-4ef3-a845-342ebbd1b96b
-- title:
--   §1, p.4 — removing redundant OR-arcs
-- statement:
--   Let $I$ be an instance with acyclic AND-precedences, and let $I^\circ$ be the instance obtained by deleting every redundant OR-arc $(a,b)$, i.e. every $(a,b)\in E_\vee$ such that some other $a'\in\mathcal P(b)$ is a transitive AND-predecessor of $a$. Then
--   1. a schedule $C$ is feasible for $I$ if and only if it is feasible for $I^\circ$;
--   2. $I^\circ$ has no redundant OR-arc.
--
--   This justifies the paper's assumption that there are no redundant OR-precedence constraints, under which $\Delta$ is defined.
--
--   Differences from the source:
--   - encoding: a precedence digraph E∧ → hypothesis `Acyclic I`; reason: a precedence graph is acyclic; the paper's transitive-closure and redundancy assumptions presuppose it
--   - reading: the remark "we may assume there are no redundant OR-precedence constraints … we could remove the arc" → the two facts the remark needs: the feasible schedules are unchanged and no redundant arc is left; reason: the remark has no formal statement
--   - encoding: E∧ transitively closed (w.l.o.g.) → redundancy defined through the transitive closure `Relation.TransGen` of the AND-arcs; reason: same redundant arcs, without changing the instance
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, p.4, "We may further assume that there are no redundant OR-precedence constraints … since any feasible schedule has to schedule a′ before a."

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_nonRedPred
import Definitions.Def_AndOrSched_reduceOr
open scoped Classical NNReal

namespace AndOrSched

/-- §1, p.4 (Happach, Schulz, arXiv:2001.07011v1): "We may further assume that there are no redundant OR-precedence constraints,
i.e. if (a, b) ∈ E∨ and (a′, a) ∈ E∧, then (a′, b) ∉ E∨. Otherwise we could remove the arc (a, b)
from E∨, since any feasible schedule has to schedule a′ before a."

For an instance with acyclic AND-precedences, removing every redundant OR-arc does not change the
set of feasible schedules, and the reduced instance has no redundant OR-arc.

**Formalization Note** Redundancy is taken with respect to the transitive closure of the
AND-arcs (the paper assumes `E∧` transitively closed). -/
theorem section_1_redundant_or_arcs (I : Instance) (hI : Acyclic I) :
    (∀ C : I.N → ℝ, IsFeasible I C ↔ IsFeasible (reduceOr I) C) ∧
    ∀ b, nonRedPred (reduceOr I) b = orPred (reduceOr I) b := by sorry

end AndOrSched
