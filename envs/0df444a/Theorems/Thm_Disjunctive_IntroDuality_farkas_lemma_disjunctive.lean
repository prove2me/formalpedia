-- Prove2me | Theorems.Thm_Disjunctive_IntroDuality_farkas_lemma_disjunctive
-- name    : Disjunctive.IntroDuality.farkas_lemma_disjunctive
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:03:24.36498+00:00
-- url     : https://prove2.me/theorems/770daf5f-1214-4901-94bf-be9074745bf5
-- title:
--   Theorem 1.2 — Farkas' Lemma for Disjunctive Sets
-- statement:
--   This is Theorem 1.2 of Balas's *Disjunctive Programming*, the disjunctive generalization of
--   Farkas' Lemma: a characterization of every valid inequality for a **disjunctive set**, i.e. a
--   union of finitely many polyhedra.
--
--   Let $Q$ be a finite index set, and for each $h \in Q$ let $A_h$ be an $m_h \times n$ matrix and
--   $b_h \in \mathbb{R}^{m_h}$, defining the polyhedron $P_h := \{x \in \mathbb{R}^n : A_h x \ge
--   b_h\}$. Let $F := \bigcup_{h \in Q} P_h$ be the disjunctive set they form, and let $Q^* :=
--   \{h \in Q : P_h \ne \emptyset\}$. Then, for $\alpha \in \mathbb{R}^n$ and $\alpha_0 \in
--   \mathbb{R}$:
--
--   $$
--   \big(\forall x \in F,\ \alpha x \ge \alpha_0\big) \iff \Big(\forall h \in Q^*,\ \exists\, u_h
--   \ge 0 \text{ with } u_h A_h = \alpha \text{ and } \alpha_0 \le u_h b_h\Big).
--   $$
--
--   The forward direction reduces to the classical (single-polyhedron) Farkas' Lemma applied
--   separately to each nonempty $P_h$: an inequality is valid for a union exactly when it is valid
--   for every piece of the union, and validity for a single polyhedron is certified by ordinary
--   Farkas multipliers. The theorem is the starting point for describing the whole family of valid
--   inequalities — hence cutting planes — for a disjunctive program, and specializes (for $|Q|=1$)
--   to ordinary Farkas' Lemma.
--
--   **Formalization Note.** This theorem is about a genuine union of possibly-differently-shaped
--   polyhedra ($m_h$ may depend on $h$), which is a different and strictly more general statement
--   than the single-polyhedron Farkas' Lemma already on the platform (`SmaleNinth.farkas_lemma`);
--   it is not restated as a reference to that theorem. `dotProduct` is Mathlib's `⬝ᵥ` and
--   `Matrix.vecMul u A` is the row-vector product $uA$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 9, Theorem 1.2

import Mathlib
import Definitions.Def_Disjunctive_IntroDuality_PolyhedralSystems

namespace Disjunctive.IntroDuality

/-- Theorem 1.2 (Balas §1.4, p. 9, [6, 8], Farkas' Lemma for Disjunctive Sets): the inequality
`α x ≥ α₀` is satisfied by every point of the disjunctive set `F = ⋃_{h ∈ Q} P_h` if and only if
for every `h` with `P_h` nonempty there is a multiplier `u_h ≥ 0` with `α = u_h A_h` and
`α₀ ≤ u_h b_h`. -/
theorem farkas_lemma_disjunctive {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (α : Fin n → ℝ) (α0 : ℝ) :
    (∀ x ∈ ⋃ h : Q, Poly (A h) (b h), α0 ≤ dotProduct α x) ↔
      ∀ h : Q, (Poly (A h) (b h)).Nonempty →
        ∃ u : Fin (m h) → ℝ, 0 ≤ u ∧ Matrix.vecMul u (A h) = α ∧
          α0 ≤ dotProduct u (b h) := by sorry

end Disjunctive.IntroDuality
