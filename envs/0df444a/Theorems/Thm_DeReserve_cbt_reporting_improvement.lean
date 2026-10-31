-- Prove2me | Theorems.Thm_DeReserve_cbt_reporting_improvement
-- name    : DeReserve.cbt_reporting_improvement
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:53.445991+00:00
-- url     : https://prove2.me/theorems/e4e6cde9-1373-48ee-9b56-f526e6cb2619
-- title:
--   Proof of Theorem 3, part (ii) (p.36): reporting membership is an improvement for $C^{BT}_s$
-- statement:
--   Let $i$ be a member of a reserve category $r\in\mathcal R$, fix an institution $s$ and the reports of the others, and let $C^{BT}_s$ and $\tilde C^{BT}_s$ be the backward transfers rules $i$ faces when she reports GC and when she reports $r$. Then $\tilde C^{BT}_s$ is an improvement over $C^{BT}_s$ for $i$ (Afacan 2017, Definition 8): for every set $A$,
--
--   1. if $i\in C^{BT}_s(A)$ then $i\in\tilde C^{BT}_s(A)$;
--   2. if $i\notin C^{BT}_s(A)\cup\tilde C^{BT}_s(A)$ then $C^{BT}_s(A)=\tilde C^{BT}_s(A)$.
--
--   Through Afacan's Theorem 2 this yields that DA-BT cannot be manipulated by withholding membership. The paper attributes the claim to "Theorem 2"; its own Theorem 2 is Pareto dominance, so the claim is cited by page.
--
--   Differences from the source:
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant → the last iteration is searched among the first q^OBC_s + 1 iterations; reason: q^OBC strictly decreases at every non-final iteration, so the bound is never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Proof of Theorem 3, part (ii), p.36

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **Reporting membership is an improvement.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Proof of Theorem 3, part (ii), p.36:
for a member `i` of a reserve category `r` (`t_i = r`), the backward transfers rule
`C̃^BT_s` that `i` faces when reporting `r` is an improvement (Afacan 2017, Def. 8) over the rule
`C^BT_s` she faces when reporting `GC`: for every `A`, (i) `i ∈ C^BT_s(A) ⇒ i ∈ C̃^BT_s(A)` and
(ii) `i ∉ C^BT_s(A) ∪ C̃^BT_s(A) ⇒ C^BT_s(A) = C̃^BT_s(A)`. -/
theorem cbt_reporting_improvement {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    ∀ (s : S) (T : I → CatMembership) (i : I) (r : Res), T i = some r →
      IsImprovement (chosenBT (pri s) T (q s)) (chosenBT (pri s) (Function.update T i none) (q s))
        i := by sorry

end DeReserve
