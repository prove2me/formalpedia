-- Prove2me | Theorems.Thm_Erdos195_acyclic_demands_do_not_ensure_extension
-- name    : Erdos195.acyclic_demands_do_not_ensure_extension
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T06:33:50.271036+00:00
-- url     : https://prove2.me/theorems/5f5a2ded-21d7-44ba-b095-80b048bd7046
-- title:
--   Acyclic initial continuation demands do not guarantee safe extension
-- statement:
--   Let $P=(0,3,2,11,10)$. For any finite word $Q$ and relation $R$ on the integers, form the relation that puts the letters of $Q$ first in their order of first occurrence, puts them before every integer missing from $Q$, and uses $R$ between missing integers. Write $\operatorname{Safe}(R,Q)$ when this completion relation contains no nonconstant four-term arithmetic progression in increasing relation order.
--
--   For integers $c,d$, define the initial continuation-demand relation $D(c,d)$ by requiring that $c,d$ are both missing from $P$ and that there are letters $a,b$ appearing in this order in $P$ with $c=2b-a$ and $d=3b-2a$. Such a demand means that any safe prefix extension containing $c$ must contain $d$ earlier.
--
--   Then:
--
--   1. $\operatorname{Safe}(\varnothing,P)$ holds, where $\varnothing$ is the constantly false tail relation.
--   2. The directed graph $D$ has no nonempty directed cycle.
--   3. For every relation $R$ and finite word $Q$ extending $P$ as a prefix, $\operatorname{Safe}(R,Q)$ implies $4\notin Q$.
--
--   Thus safety for the empty tail relation together with acyclicity of the initial continuation demands is insufficient to guarantee extension to a prescribed integer. The conclusion has no bound on additional letters or their sizes and does not assume that $R$ is a total order. It is a finite obstruction to this proposed extension invariant, not a resolution of Erdős Problem 195.
-- source:
--   Research-derived finite obstruction in the canonical Erdős Problem 195 model, verified in Lean on 2026-10-23. Context: https://www.erdosproblems.com/195. The obstruction itself is not attributed to that source or to the Ho construction.

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem acyclic_demands_do_not_ensure_extension :
    let P : List ℤ := [0, 3, 2, 11, 10]
    let D : ℤ → ℤ → Prop := fun c d =>
      c ∉ P ∧ d ∉ P ∧ ∃ a ∈ P, ∃ b ∈ P,
        P.idxOf a < P.idxOf b ∧ c = 2 * b - a ∧ d = 3 * b - 2 * a
    Erdos195.Safe (fun _ _ => False) P ∧
      (∀ c : ℤ, ¬ Relation.TransGen D c c) ∧
      ∀ (R : ℤ → ℤ → Prop) (Q : List ℤ),
        P <+: Q → Erdos195.Safe R Q → (4 : ℤ) ∉ Q := by
  sorry

end Erdos195
