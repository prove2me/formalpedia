-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_iterated_split_convexification
-- name    : Disjunctive.HigherDim.iterated_split_convexification
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:38:52.823577+00:00
-- url     : https://prove2.me/theorems/42f162cb-5825-4e86-b538-e5c2ad5a6d93
-- title:
--   Theorem 7.2 — iterating split convexification over a fixed sequence
-- statement:
--   This is Theorem 7.2 of Balas's *Disjunctive Programming*: applying $P_j$ repeatedly
--   over an explicit, duplicate-free sequence of coordinates $i_1,\dots,i_t$ reaches the convex hull
--   of imposing $0/1$ on all of them at once.
--
--   $$
--   P_{i_1,\dots,i_t}(K) = \mathrm{conv}(K \cap \{x \in \mathbb R^n : x_j \in \{0,1\},\ j =
--   i_1,\dots,i_t\}).
--   $$
--
--   The book proves this, together with its Corollary 7.3, "directly from Theorem 3.1 on the
--   sequential convexifiability of facial disjunctive programs, of which the mixed 0-1 program is a
--   special case" — the mixed 0-1 disjunctive set is facial, so sequential convexification over *any*
--   order of its disjunctions reaches the same hull, matching `03-sequential-convex`'s own goal
--   theorem specialized to split disjunctions.
--
--   **Formalization Note.** `l : List (Fin n)` with `l.Nodup` represents the coordinate sequence
--   $i_1,\dots,i_t$ explicitly (order matters for `IteratedSplit`'s literal left-fold definition, even
--   though the theorem's conclusion is order-independent); `l.toFinset` is the resulting index set on
--   the right.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 93, Theorem 7.2

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic

namespace Disjunctive.HigherDim

/-- Theorem 7.2 (Balas §7.1, p. 92): iterating one-variable convexification over a fixed,
duplicate-free sequence of coordinates yields the convex hull of imposing `0/1` on all of them
at once. -/
theorem iterated_split_convexification {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (l : List (Fin n)) (hnd : l.Nodup) :
    IteratedSplit (Poly A b) l = convexHull ℝ (Poly A b ∩ ⋂ j ∈ l.toFinset, ZeroOneSet j) := by sorry

end Disjunctive.HigherDim
