-- Prove2me | Theorems.Thm_Disjunctive_SequentialConvex_halfspace_intersection_convexity
-- name    : Disjunctive.SequentialConvex.halfspace_intersection_convexity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:25:06.271701+00:00
-- url     : https://prove2.me/theorems/a336e6c4-df58-4117-a74b-a9fb734e974d
-- title:
--   Lemma 3.2 — a halfspace-intersection lemma for unions of polyhedra
-- statement:
--   This is Lemma 3.2 of Balas's *Disjunctive Programming*, the auxiliary result the book names
--   explicitly as what Theorem 3.1's proof needs.
--
--   Let $P_1,\dots,P_r$ be finitely many polyhedra and $P := \bigcup_{h=1}^r P_h$. Let $H^+ :=
--   \{x : dx \le d_0\}$ be a halfspace and $H^- := \{x : dx \ge d_0\}$ its (weak) complement.
--   If $P \subseteq H^+$, then
--
--   $$
--   H^- \cap \mathrm{conv}(P) = \mathrm{conv}(H^- \cap P).
--   $$
--
--   Intuitively: since every piece of $P$ lies entirely on the $H^+$ side, any convex combination
--   of points of $P$ that lands in $H^-$ must, term by term, only use points of $P$ that
--   themselves already lie in $H^- \cap P$ — combinations cannot "average their way" past the
--   boundary from the $H^+$ side. This is exactly the halfspace-commutes-with-convexification step
--   Theorem 3.1's induction needs at each stage of the recursion.
--
--   **Formalization Note.** `Poly` is the plain polyhedron `{x : Ax ≥ b}` (no nonnegativity),
--   matching the Lemma's own unrestricted `P_h`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 43, Lemma 3.2

import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic

namespace Disjunctive.SequentialConvex

/-- Lemma 3.2 (Balas §3.1, p. 43), the auxiliary result Theorem 3.1's proof rests on: if a union
of finitely many polyhedra `P` lies in a halfspace `H⁺`, then intersecting `conv P` with the
opposite halfspace `H⁻` commutes with taking the convex hull. -/
theorem halfspace_intersection_convexity {n r : ℕ} {m : Fin r → ℕ}
    (A : (h : Fin r) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Fin r) → Fin (m h) → ℝ)
    (d : Fin n → ℝ) (d0 : ℝ) (hSub : (⋃ h : Fin r, Poly (A h) (b h)) ⊆ HalfspaceLE d d0) :
    HalfspaceGE d d0 ∩ convexHull ℝ (⋃ h : Fin r, Poly (A h) (b h)) =
      convexHull ℝ (HalfspaceGE d d0 ∩ ⋃ h : Fin r, Poly (A h) (b h)) := by sorry

end Disjunctive.SequentialConvex
