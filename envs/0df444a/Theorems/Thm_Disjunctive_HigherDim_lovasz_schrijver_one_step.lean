-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_lovasz_schrijver_one_step
-- name    : Disjunctive.HigherDim.lovasz_schrijver_one_step
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:40:12.053995+00:00
-- url     : https://prove2.me/theorems/a39935e6-b24e-45a4-b377-c2d2c4b7f14e
-- title:
--   Theorem 7.4 — N(K) is contained in every one-variable convex hull
-- statement:
--   This is Theorem 7.4 of Balas's *Disjunctive Programming*, cited to Lovász and
--   Schrijver [99]:
--
--   $$
--   N(K) \subseteq \mathrm{conv}(K \cap \{x \in \mathbb R^n : x_j \in \{0,1\}\}), \quad j =
--   1,\dots,p.
--   $$
--
--   The book's own one-line proof: "Theorem 7.1 implies Theorem 7.4, since $N(K) \subseteq P_j(K)$" —
--   the Lovász-Schrijver lift, which sets $y_{ij} = y_{ji}$ for *all* pairs before projecting, is at
--   least as tight as the single-variable lift $P_j(K)$ for every $j$, so Theorem 7.1's identification
--   of $P_j(K)$ with the one-variable convex hull immediately bounds $N(K)$.
--
--   **Formalization Note.** Stated for every $j \in N'$ simultaneously (`∀ j ∈ N', ...`), matching the
--   theorem's own "$j = 1,\dots,p$" universal quantification; `NOp`/`ZeroOneSet` are `Lifts`'s and
--   `Basic`'s definitions respectively.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 94, Theorem 7.4

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts

namespace Disjunctive.HigherDim

/-- Theorem 7.4 (Balas §7.2, p. 93, [99]): the Lovász-Schrijver lift `N(K)` sits inside the
one-variable convex hull for every `j` in the 0-1 index set. -/
theorem lovasz_schrijver_one_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) :
    ∀ j ∈ Nprime, NOp A b Nprime ⊆ convexHull ℝ (Poly A b ∩ ZeroOneSet j) := by sorry

end Disjunctive.HigherDim
