-- Prove2me | Theorems.Thm_Disjunctive_NormalForms_basic_step_dnf
-- name    : Disjunctive.NormalForms.basic_step_dnf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:27:47.379979+00:00
-- url     : https://prove2.me/theorems/65cfdf1a-1fee-4917-8b6e-71e02cfac6ea
-- title:
--   Theorem 4.1 — the basic-step DNF identity
-- statement:
--   This is Theorem 4.1 of Balas's *Disjunctive Programming*, the identity underlying the "basic
--   step" that converts a regular form to DNF one conjunct at a time.
--
--   For unions of polyhedra $S_k = \bigcup_{i \in Q_k} P_i$ and $S_l = \bigcup_{j \in Q_l} P_j$:
--
--   $$
--   S_k \cap S_l = \bigcup_{(i,j) \in Q_k \times Q_l} (P_i \cap P_j).
--   $$
--
--   This is exactly the distributivity of $\cup$ over $\cap$, and it is the whole content of the
--   "basic step": replacing two conjuncts of a regular form by their intersection, expressed in DNF as
--   a union over all pairs. Applying this identity $|T|-1$ times to a regular form with $|T|$
--   conjuncts, merging two at a time, brings any disjunctive set to DNF while preserving regularity at
--   every intermediate stage — the iterative process `IsBasicStepOf` captures step-by-step in the
--   companion definition and Theorem 4.7's hypothesis chain.
--
--   **Formalization Note.** This is the single-step identity (4.2); the "brought to DNF in `|T|-1`
--   applications" claim is a direct corollary of iterating it, and is the content of the
--   `IsBasicStepOf` chain used by Theorem 4.7, not restated as a separate counting argument here.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 49, Theorem 4.1

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

/-- Theorem 4.1 (Balas §4.1, p. 49, [12]), the basic-step identity: the intersection of two
unions of polyhedra is itself the union, over all pairs, of the pairwise intersections — the
DNF of `S_k ∩ S_l` given by (4.2). -/
theorem basic_step_dnf {n : ℕ} {Qk Ql : Type*} [Fintype Qk] [Fintype Ql] (mk : Qk → ℕ)
    (Ak : (i : Qk) → Matrix (Fin (mk i)) (Fin n) ℝ) (bk : (i : Qk) → Fin (mk i) → ℝ)
    (ml : Ql → ℕ) (Al : (j : Ql) → Matrix (Fin (ml j)) (Fin n) ℝ) (bl : (j : Ql) → Fin (ml j) → ℝ) :
    (⋃ i : Qk, Poly (Ak i) (bk i)) ∩ (⋃ j : Ql, Poly (Al j) (bl j)) =
      ⋃ p : Qk × Ql, Poly (Ak p.1) (bk p.1) ∩ Poly (Al p.2) (bl p.2) := by sorry

end Disjunctive.NormalForms
