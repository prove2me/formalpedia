-- Prove2me | Theorems.Thm_BiAbduction_Systematic_lemma_3_19
-- name    : BiAbduction.Systematic.lemma_3_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:15:03.973813+00:00
-- url     : https://prove2.me/theorems/e1b968d2-cce2-4662-b8c2-11e483a7493b
-- title:
--   Lemma 3.19 — a solution derived in the Figure 2 system is ≤c-below every solution
-- statement:
--   Let $\Delta$ be a quantifier-free left-hand side and $H$ a symbolic heap of the Points-to Instantiation, with no variable bound in $H$ occurring in $\Delta$. If $\Delta*[D]\triangleright H$ is derivable and $F$ is an arbitrary predicate (set of states) with $\Delta*F\models H$, then
--   $$D\le_c F,$$
--   where $\le_c$ is the compatible preorder relative to the same $\Delta$: $(F\wedge\mathrm{Elsewhere}(\Delta))\models (D\wedge\mathrm{Elsewhere}(\Delta))*\mathsf{true}$.
--
--   With the soundness of Figure 2 this says that every derivable $D$ is a minimal solution w.r.t. $\le_c$, the first phase of the systematic algorithm.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 29, Lemma 3.19

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Rules

namespace BiAbduction.Systematic

/-- Lemma 3.19 (p. 29). If `Δ ∗ [D] ▷ H` is derivable and `Δ ∗ F ⊨ H` for a predicate `F`, then
`D ≤c F` (the `≤c` relative to the same `Δ`). -/
theorem lemma_3_19 (Δ : LHS) (D : Disj) (H : SH) (hconv : Conv Δ H)
    (hder : Derives Δ D H) (F : Pred) (hF : IsSolution (lhsDen Δ) (shDen H) F) :
    CompatLe (lhsDen Δ) (disjDen D) F := by sorry

end BiAbduction.Systematic
