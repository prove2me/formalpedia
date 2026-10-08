-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_omega_contains_optimal
-- name    : FedergruenTzur.MinPred.omega_contains_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:54:44.992775+00:00
-- url     : https://prove2.me/theorems/0f8fadf5-cf86-4eef-b2fc-c99279308510
-- title:
--   §2, p. 915: Ω(j) contains a (globally) optimal terminal order period for the horizon t = j
-- statement:
--   In the dynamic lot size model with costs given by the recursion (2), let $j \ge 1$ and let $\Omega(j)$ be the $j$th Minimal Optimal Predecessors list. Then there is a period $l \in \Omega(j)$ that is an optimal last setup period for the horizon $j$:
--   $$
--   \exists\, l \in \Omega(j): \quad F(l, j) = F(j).
--   $$
--   In particular $\Omega(j)$ is nonempty.
--
--   This is the property that makes it sufficient for the forward algorithm to search for the optimal last setup period $l(j)$ inside the list $\Omega(j)$.
--
--   **Formalization Note.** $\Omega(j)$ is taken in the open-interval reading of the definition item `Omega`; the statement holds for arbitrary real data.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 915, §2, second paragraph ('Clearly, Ω(j) contains a (globally) optimal terminal order period for the horizon t = j')

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega

namespace FedergruenTzur.MinPred

open LotSizing

/-- §2, p. 915, second paragraph: "Clearly, `Ω(j)` contains a (globally) optimal terminal order
period for the horizon `t = j`." In particular `Ω(j)` is nonempty. -/
theorem omega_contains_optimal (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) :
    ∃ l ∈ P.Omega j, P.Flast l j = P.Fopt j := by sorry

end FedergruenTzur.MinPred
