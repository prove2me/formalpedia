-- Prove2me | Theorems.Thm_Disjunctive_Polarity_scaled_polar_eq_W0_section
-- name    : Disjunctive.Polarity.scaled_polar_eq_W0_section
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:22:59.296257+00:00
-- url     : https://prove2.me/theorems/eb69b2dd-afd1-4360-b174-63ce83b0e2de
-- title:
--   Corollary 2.17 — the scaled polar as a section of $W_0$
-- statement:
--   This is Corollary 2.17 of Balas's *Disjunctive Programming* (not found by
--   `statements.jsonl`'s regex extraction; verified directly against the PDF), the direct link between
--   the polarity route and the projection-cone route to $\mathrm{cl}\,\mathrm{conv}(F)$.
--
--   $$
--   F_{(\alpha_0)} = \{\alpha \in \mathbb{R}^n : (\alpha,\alpha_0) \in W_0\},
--   $$
--
--   i.e. the scaled polar of the disjunctive set $F$ at level $\alpha_0$ is exactly the
--   $\alpha$-section of the cone $W_0$ at that $\alpha_0$. This follows directly from Theorem 1.2's
--   disjunctive Farkas' Lemma: the family of valid inequalities for $F$ at level $\alpha_0$ (which is
--   exactly $F_{(\alpha_0)}$) is characterized by per-disjunct multipliers $u_h \ge 0$ with
--   $u_h A_h = \alpha$, $\alpha_0 \le u_h b_h$ — precisely the defining condition of $W_0$.
--
--   **Formalization Note.** This is the direct predecessor step to Theorem 2.18's proof, which reduces
--   facets of $\mathrm{cl}\,\mathrm{conv}(F)$ to vertices of $F_{(\alpha_0)}$ via this
--   identification.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 35, Corollary 2.17

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Polars

namespace Disjunctive.Polarity

/-- Corollary 2.17 (Balas §2.4, p. 35; not in `statements.jsonl`'s regex extraction): the scaled
polar of the disjunctive set `F` at level `α₀` is exactly the `α`-section of `W₀` at that `α₀`. -/
theorem scaled_polar_eq_W0_section {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) (α0 : ℝ) :
    ScaledPolar (DisjunctiveSet m A b) α0 = {α : Fin n → ℝ | (α, α0) ∈ W0 m A b} := by sorry

end Disjunctive.Polarity
