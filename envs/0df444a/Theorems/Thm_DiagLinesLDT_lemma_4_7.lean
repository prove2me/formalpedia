-- Prove2me | Theorems.Thm_DiagLinesLDT_lemma_4_7
-- name    : DiagLinesLDT.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:54:50.721634+00:00
-- url     : https://prove2.me/theorems/1606b723-9496-49b2-b91e-432c0fd4819f
-- title:
--   Lemma 4.7 — symplectic product of point labels
-- statement:
--   For all $(x,y),(x',y')\in\mathbb F_q^2$,
--
--   $$\langle w(x,y),w(x',y')\rangle=(x'-x)(y'-y)^2.$$
--
--   The product vanishes exactly when the two points lie on a common axis-parallel line, which is the property the label map was chosen for.
--
--   Differences from the source:
--   - generalization: 𝔽_q with q an odd prime → any field; reason: the identity is ring algebra; §§7.1 and 7.2 use it in every characteristic, and it specializes to the printed statement
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Lemma 4.7, p.10

import Mathlib
import Definitions.Def_DiagLinesLDT_labelMap

namespace DiagLinesLDT

/-- Symplectic product of point labels.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Lemma 4.7, p.10.

**Formalization Note** `u = (x, y)`, `v = (x', y')`. Stated over every field; the source uses it in
every characteristic (Proposition 7.1, p.22; §7.2, p.23). -/
theorem lemma_4_7 {F : Type*} [Field F] (u v : Fin 2 → F) :
    symp (w u) (w v) = (v 0 - u 0) * (v 1 - u 1) ^ 2 := by sorry

end DiagLinesLDT
