-- Prove2me | Theorems.Thm_Disjunctive_LiftProject_cglp_lifting_from_restricted
-- name    : Disjunctive.LiftProject.cglp_lifting_from_restricted
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:36:06.393093+00:00
-- url     : https://prove2.me/theorems/20e5d7d8-4c90-4e4f-8640-d61cca11790f
-- title:
--   Theorem 6.2 — CGLP lifting from a restricted solution
-- statement:
--   This is Theorem 6.2 of Balas's *Disjunctive Programming*: an explicit construction lifting
--   an optimal solution of the reduced cut-generating LP `(CGLP)^R` back to the full `(CGLP)`.
--
--   Given an optimal $w^R = (\alpha^R, u^R, u^R_0, v^R, v^R_0)$ for `(CGLP)^R`, extend it to $\bar w$
--   by keeping $\bar u_0 = u^R_0$, $\bar v_0 = v^R_0$ unchanged, and, for each variable $i$ outside
--   the restricted set $R$, introducing a new multiplier component
--
--   $$
--   \bar u_{\text{new}}(i) = \max\{0,\ \alpha^2_i - \alpha^1_i\}, \qquad
--   \bar v_{\text{new}}(i) = \max\{0,\ \alpha^1_i - \alpha^2_i\}
--   $$
--
--   (with $\alpha^1_i, \alpha^2_i$ the row-restricted dot products $u^R \tilde A^R_i$, $v^R \tilde
--   A^R_i$), so that $\bar\alpha_i = \alpha^1_i + \bar u_{\text{new}}(i) = \max\{\alpha^1_i,
--   \alpha^2_i\}$ for $i \notin R$. This is what makes lift-and-project cuts practical at scale:
--   solving the (much smaller) reduced LP over only the *active* variables, then reading off the full
--   cut's coefficients in closed form, without re-solving over the full variable set.
--
--   **Formalization Note.** The book's own construction names two families of new rows
--   (`ū_{m+i}`, `ū_{m+n+i}`) tied to specific row-block positions of the augmented constraint matrix;
--   this item captures the substantive extension values (the `uExtra`/`vExtra` used by the `ᾱ`
--   formula) rather than committing to that literal row-indexing scheme, which the source text does
--   not fully disambiguate for variables outside the 0-1 index set — see `MODERATION_NOTES.md`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 84, Theorem 6.2

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic

namespace Disjunctive.LiftProject

/-- Theorem 6.2 (Balas §6.4, p. 84, [19]): an **optimal** solution `w^R` to the reduced
`(CGLP)^R` extends to a solution `w̄` of the full `(CGLP)` — over the extended row space
`M ⊕ Fin n`, whose fresh rows are the deleted bound constraints — with `ū₀ = u^R_0`,
`v̄₀ = v^R_0`, the new multiplier components at `i ∉ R` given by the displayed max/zero case
split, and `ᾱ_i = ū Ã^R_i` for `i ∉ R`; and `w̄` is **feasible and optimal for `(CGLP)`**, which
is the theorem's content. Asserting only that the displayed quantities exist says nothing: they
are defined by explicit formulas. The objective is the cut violation `α x̄ − β` at the point
`x̄` being separated (p. 85, "any solution that minimizes `α x̄ − β`"). -/
theorem cglp_lifting_from_restricted {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (MR : Finset M) (R : Finset (Fin n)) (j : Fin n)
    (xbar : Fin n → ℝ) (αR : Fin n → ℝ) (uR vR : M → ℝ) (u0R v0R βR : ℝ)
    (hfeas : IsCGLPRFeasible Atil btil MR R j αR uR u0R vR v0R βR)
    (hopt : ∀ (α' : Fin n → ℝ) (u' v' : M → ℝ) (u0' v0' β' : ℝ),
      IsCGLPRFeasible Atil btil MR R j α' u' u0' v' v0' β' →
        dotProduct αR xbar - βR ≤ dotProduct α' xbar - β') :
    ∃ (α : Fin n → ℝ) (u v : M ⊕ Fin n → ℝ),
      (∀ ρ : M, u (Sum.inl ρ) = uR ρ ∧ v (Sum.inl ρ) = vR ρ) ∧
      (∀ i ∉ R, u (Sum.inr i) =
          (if Alpha1 Atil uR MR i < Alpha2 Atil vR MR i
            then Alpha2 Atil vR MR i - Alpha1 Atil uR MR i else 0) ∧
        v (Sum.inr i) =
          (if Alpha2 Atil vR MR i < Alpha1 Atil uR MR i
            then Alpha1 Atil uR MR i - Alpha2 Atil vR MR i else 0)) ∧
      (∀ i ∈ R, u (Sum.inr i) = 0 ∧ v (Sum.inr i) = 0) ∧
      (∀ i ∈ R, α i = αR i) ∧
      (∀ i ∉ R, α i = Alpha1 Atil uR MR i + u (Sum.inr i)) ∧
      IsCGLPFeasible (AtilExt Atil) (BtilExt btil) j α u u0R v v0R βR ∧
      ∀ (α' : Fin n → ℝ) (u' v' : M ⊕ Fin n → ℝ) (u0' v0' β' : ℝ),
        IsCGLPFeasible (AtilExt Atil) (BtilExt btil) j α' u' u0' v' v0' β' →
          dotProduct α xbar - βR ≤ dotProduct α' xbar - β' := by sorry

end Disjunctive.LiftProject
