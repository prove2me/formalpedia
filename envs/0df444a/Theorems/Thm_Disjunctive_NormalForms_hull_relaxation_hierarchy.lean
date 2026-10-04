-- Prove2me | Theorems.Thm_Disjunctive_NormalForms_hull_relaxation_hierarchy
-- name    : Disjunctive.NormalForms.hull_relaxation_hierarchy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:29:28.283996+00:00
-- url     : https://prove2.me/theorems/bc90479b-334e-43b7-b7f4-eed2038bbb1c
-- title:
--   Theorem 4.7 — the hull-relaxation hierarchy
-- statement:
--   This is Theorem 4.7 of Balas's *Disjunctive Programming*, the goal theorem of this mission:
--   a chain of tightening relaxations connecting the CNF of a disjunctive set to its exact convex hull
--   in DNF.
--
--   Let $F_0, F_1, \dots, F_t$ be a sequence of regular forms of the same disjunctive set, with $F_0$
--   in CNF (polyhedral part $P_0$), $F_t$ in DNF, and each $F_i$ obtained from $F_{i-1}$ by a basic
--   step. Then
--
--   $$
--   P_0 = h\text{-}\mathrm{rel}(F_0) \supseteq h\text{-}\mathrm{rel}(F_1) \supseteq \cdots
--   \supseteq h\text{-}\mathrm{rel}(F_t) = \mathrm{cl}\,\mathrm{conv}(F_t).
--   $$
--
--   The first equality is Lemma 4.5; each inclusion is Lemma 4.6, applied to the pair of conjuncts
--   merged at that step; the last equality is the definition of hull-relaxation for a single conjunct
--   (DNF has $|T_t|=1$). The practical content: starting from the ordinary LP relaxation $P_0$ of a
--   CNF-stated combinatorial problem, performing basic steps and re-taking hull-relaxations produces a
--   *monotonically tightening* sequence of polyhedral relaxations that terminates exactly at the true
--   convex hull — a computational strategy for approaching $\mathrm{cl}\,\mathrm{conv}(F)$
--   incrementally rather than all at once.
--
--   **Formalization Note.** The three parts of the chain (initial equality, the step-by-step
--   containments, final equality) are stated as a conjunction rather than a single chained inequality,
--   since Lean has no native notation for a mixed equality/containment chain of this shape;
--   `hull-relaxation ≠ convex hull` is preserved throughout — only the *last* term of the chain is
--   asserted equal to `cl conv F_t`, matching the chapter's own warning that earlier terms are
--   generally strictly larger.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 53, Theorem 4.7

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

/-- Theorem 4.7 (Balas §4.2, p. 53-54): for a sequence of regular forms `F_0, …, F_t` of a
disjunctive set, with `F_0` in CNF, `F_t` in DNF, and each `F_i` obtained from `F_{i-1}` by a
basic step, the hull-relaxations form a chain `P₀ = h-relF₀ ⊇ h-relF₁ ⊇ ⋯ ⊇ h-relF_t = cl conv
F_t`. -/
theorem hull_relaxation_hierarchy {n t : ℕ} (T : Fin (t + 1) → Type*) [∀ i, Fintype (T i)]
    (S : (i : Fin (t + 1)) → T i → Set (Fin n → ℝ)) (hCNF : ∀ j, IsElementaryDisjunction (S 0 j))
    (hDNF : Fintype.card (T (Fin.last t)) = 1)
    (hSteps : ∀ i : Fin t, IsBasicStepOf (S i.castSucc) (S i.succ)) :
    P0Set (S 0) = HRel (S 0) ∧
      (∀ i : Fin t, HRel (S i.succ) ⊆ HRel (S i.castSucc)) ∧
      HRel (S (Fin.last t)) = closure (convexHull ℝ (⋂ j, S (Fin.last t) j)) := by sorry

end Disjunctive.NormalForms
