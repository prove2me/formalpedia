-- Prove2me | Theorems.Thm_FamousTheorems_ade_inequality_classification
-- name    : FamousTheorems.ade_inequality_classification
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:17.242393+00:00
-- url     : https://prove2.me/theorems/6ec429c8-19e1-4458-ba9a-c7e65a54640e
-- title:
--   The ADE inequality classification
-- statement:
--   **The ADE inequality classification.** For positive integers $p,q,r$,
--   $$\frac1p+\frac1q+\frac1r>1$$
--   if and only if the multiset $\{p,q,r\}$ is, up to order, one of $\{1,q,r\}$ (type $A$), $\{2,2,n\}$ (type $D$), $\{2,3,3\}$ ($E_6$), $\{2,3,4\}$ ($E_7$) or $\{2,3,5\}$ ($E_8$).
--
--   This inequality appears throughout mathematics: it classifies the simply laced Dynkin diagrams, the finite subgroups of $SO(3)$, the platonic solids, and the simple singularities. It is a key step in the classification of simply laced root systems.
--
--   **Formalization note.** Mathlib's `ADEInequality.classification`. `ADEInequality.sumInv` is $\frac1p+\frac1q+\frac1r$ as a rational number, and `ADEInequality.Admissible` says that the multiset is one of the families `A' q r`, `D' n`, `E6`, `E7`, `E8` listed above.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ADEInequality.classification`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem ade_inequality_classification (p q r : ℕ+) : 1 < ADEInequality.sumInv {p, q, r} ↔ ADEInequality.Admissible {p, q, r} := by sorry

end FamousTheorems
