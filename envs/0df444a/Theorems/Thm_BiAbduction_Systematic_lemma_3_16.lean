-- Prove2me | Theorems.Thm_BiAbduction_Systematic_lemma_3_16
-- name    : BiAbduction.Systematic.lemma_3_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:02.957915+00:00
-- url     : https://prove2.me/theorems/8d2b7370-fdd3-41fa-9891-8d36a3cacd3e
-- title:
--   Lemma 3.16 — min(D ∨ ¬Elsewhere(Δ)) is the ≾-minimal solution when D is ≤c-minimal
-- statement:
--   Let $\Delta$ and $H$ be predicates and consider the abduction question $\Delta*M\models H$. Let $D$ be a minimal solution w.r.t. the compatible preorder $\le_c$: $\Delta*D\models H$, and $D\le_c F$ for every predicate $F$ with $\Delta*F\models H$. Then
--   $$\min\big(D\vee\neg\mathrm{Elsewhere}(\Delta)\big)$$
--   is the minimal solution w.r.t. $\precsim$: it is a solution, and it is $\precsim$-below every solution $M'$ (every predicate with $\Delta*M'\models H$).
--
--   This lemma reduces the computation of the best solution to three phases: a $\le_c$-minimal solution, the incompatible solutions $\neg\mathrm{Elsewhere}(\Delta)$, and $\min$.
--
--   **Formalization Note** The page states the lemma for the symbolic heaps $\Delta$, $H$ of (5); its proof uses no syntax, and the statement here holds for arbitrary predicates $\Delta$, $H$, $D$, which includes the page's case.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 27, Lemma 3.16

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Semantics

namespace BiAbduction.Systematic

/-- Lemma 3.16 (p. 27). If `D` is a minimal solution of `Δ ∗ ? ⊨ H` w.r.t. `≤c`, then
`min(D ∨ ¬Elsewhere(Δ))` is the minimal solution w.r.t. `≾`. -/
theorem lemma_3_16 (Δ H D : Pred) (hD : IsCompatMinSolution Δ H D) :
    IsLeastSolution Δ H (minSet (D ∪ (Elsewhere Δ)ᶜ)) := by sorry

end BiAbduction.Systematic
