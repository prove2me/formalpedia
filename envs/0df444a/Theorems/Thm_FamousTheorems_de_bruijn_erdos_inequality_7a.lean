-- Prove2me | Theorems.Thm_FamousTheorems_de_bruijn_erdos_inequality_7a
-- name    : FamousTheorems.de_bruijn_erdos_inequality_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:59.59876+00:00
-- url     : https://prove2.me/theorems/528312b0-0f03-4fcc-8a30-ffc7c925bb34
-- title:
--   The de Bruijn–Erdős inequality: a linear space has at least as many lines as points
-- statement:
--   **The de Bruijn–Erdős inequality.** Let $(P,L)$ be a finite linear space: any two distinct points lie on a line (and, by the nondegeneracy axioms, on at most one), and the configuration is nondegenerate, meaning that no line contains all the points and no point lies on all the lines. Then there are at least as many lines as points, $|P|\le|L|$.
--
--   De Bruijn and Erdős proved this in 1948. Equality holds exactly for projective planes and for near-pencils, which consist of one line through all points but one together with the lines joining the remaining point to the others. A special case is the Sylvester–Gallai-type fact that $n$ non-collinear points in the plane determine at least $n$ lines.
--
--   **Formalization note.** Mathlib's `Configuration.HasLines.card_le`. `Configuration.HasLines P L` bundles the nondegeneracy axioms of `Configuration.Nondegenerate` with a line through any two distinct points. Nondegeneracy includes that two distinct points lie on at most one common line and that no point is on all lines and no line contains all points.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Configuration.HasLines.card_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem de_bruijn_erdos_inequality_7a (P L : Type*) [Membership P L] [Configuration.HasLines P L] [Fintype P] [Fintype L] :
    Fintype.card P ≤ Fintype.card L := by sorry

end FamousTheorems
