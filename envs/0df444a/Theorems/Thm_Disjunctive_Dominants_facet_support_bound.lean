-- Prove2me | Theorems.Thm_Disjunctive_Dominants_facet_support_bound
-- name    : Disjunctive.Dominants.facet_support_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:11:12.687861+00:00
-- url     : https://prove2.me/theorems/b0fb957e-902d-437b-b8ba-7ec154df911d
-- title:
--   Corollary 13.8 — a bound on facet support size
-- statement:
--   This is Corollary 13.8 of Balas's *Disjunctive Programming*, an immediate consequence of
--   Theorem 13.7: no facet of the dominant needs more than $\dim(P)+1$ nonzero coefficients to
--   describe, regardless of how large $n$ is.
--
--   If $\pi x \ge \beta$ defines a facet of $P^+$, then $|\{j : \pi_j \ne 0\}| \le \dim(P)+1$.
--
--   The book derives this from the remark immediately following Theorem 13.7's proof: membership
--   in $I^S$ is equivalent to $\pi x\ge1$ defining a facet of $P^S$ of dimension $|S|-1$, and since
--   $\dim(P^S)\le\dim(P)$ (a projection cannot increase dimension), $|S|-1\le\dim(P)$, i.e.
--   $|S|\le\dim(P)+1$.
--
--   **Formalization Note.** Stated directly for a general right-hand side `β` (not fixed to `1` as
--   in Theorem 13.7's own normalization), since the corollary's own claim ("every inequality
--   defining a facet of `P⁺`") is not restricted to the unit normalization Theorem 13.7 uses for
--   $I^S$ — any positive rescaling of a facet-defining inequality is still facet-defining, so this
--   is the natural generality for a support-size bound.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 221, Corollary 13.8

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

namespace Disjunctive.Dominants

/-- Corollary 13.8 (Balas §13.2, p. 221): every inequality `πx≥β` defining a facet of `P⁺` has at
most `dim(P)+1` nonzero coefficients. -/
theorem facet_support_bound {n : ℕ} (P : Set (Fin n → ℝ)) (pi : Fin n → ℝ) (beta : ℝ)
    (hfacet : IsFacet (Dominant P) ({x ∈ Dominant P | dotProduct pi x = beta})) :
    ((Finset.univ.filter (fun j => pi j ≠ 0)).card : ℤ) ≤ PolyDim P + 1 := by sorry

end Disjunctive.Dominants
