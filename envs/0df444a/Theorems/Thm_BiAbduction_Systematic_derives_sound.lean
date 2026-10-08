-- Prove2me | Theorems.Thm_BiAbduction_Systematic_derives_sound
-- name    : BiAbduction.Systematic.derives_sound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:16:18.379776+00:00
-- url     : https://prove2.me/theorems/328a3ef9-4753-4258-9ad0-d291a4676573
-- title:
--   §3.4.2 — the rules of Figure 2 derive solutions of the abduction question (5)
-- statement:
--   Let $\Delta$ be a quantifier-free left-hand side of the Points-to Instantiation, $H$ a symbolic heap and $D$ a disjunction of symbolic heaps, and assume the bound-variable convention: no variable bound in $H$ occurs in $\Delta$. If $\Delta*[D]\triangleright H$ is derivable with the rules of Figure 2, then $D$ is a solution of (5):
--   $$\Delta*D\models H.$$
--
--   Together with Lemma 3.19 this is the claim of §3.4.2 that the rules "derive a solution D to the abduction question which is minimal w.r.t. the $\le_c$ preorder"; the present statement is its solution half.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 28, §3.4.2 (first paragraph)

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Rules

namespace BiAbduction.Systematic

/-- §3.4.2 (p. 28): the rules of Figure 2 derive a solution of the abduction question (5). -/
theorem derives_sound (Δ : LHS) (D : Disj) (H : SH) (hconv : Conv Δ H)
    (hder : Derives Δ D H) :
    IsSolution (lhsDen Δ) (shDen H) (disjDen D) := by sorry

end BiAbduction.Systematic
