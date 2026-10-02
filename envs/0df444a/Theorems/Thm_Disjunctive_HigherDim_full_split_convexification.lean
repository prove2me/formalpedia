-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_full_split_convexification
-- name    : Disjunctive.HigherDim.full_split_convexification
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:39:28.32464+00:00
-- url     : https://prove2.me/theorems/fb9c5727-1e2f-45b5-9bae-677553ceaf2d
-- title:
--   Corollary 7.3 — iterating over every 0-1 index reaches conv(K0)
-- statement:
--   This is Corollary 7.3 of Balas's *Disjunctive Programming* — **not extracted by
--   `statements.jsonl`'s regex pass** (its line begins with the theorem environment's body text, not a
--   clean "Corollary 7.3" label); verified directly against the PDF and added here manually, since the
--   book names it explicitly as one of Theorem 7.6's two proof ingredients ("Now Theorem 7.6 follows
--   from Corollary 7.3 and Theorem 7.7").
--
--   $$
--   P_{1,\dots,p}(K) = \mathrm{conv}(K_0).
--   $$
--
--   Specializing Theorem 7.2 to the *full* 0-1 index sequence $1,\dots,p$ makes the right-hand side's
--   intersection cover all of $K_0$'s defining $0/1$ constraints at once, so iterating one-variable
--   convexification over every 0-1 coordinate reaches the mixed 0-1 program's own integer hull.
--
--   **Formalization Note.** Stated with an explicit `l : List (Fin n)` and a hypothesis `l.toFinset =
--   N'` (rather than hard-coding a literal enumeration $1,\dots,p$), matching Theorem 7.2's own
--   formalization; `IteratedSplit`/`K0Set` are the same definitions used throughout this mission, so
--   this item is a direct corollary of `iterated_split_convexification` under `l.toFinset = N'`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 93, Corollary 7.3

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic

namespace Disjunctive.HigherDim

/-- Corollary 7.3 (Balas §7.1, p. 92; not in `statements.jsonl`'s regex extraction): iterating
one-variable convexification over *every* 0-1 index reaches the convex hull of the mixed 0-1
program's own feasible set `K₀`. -/
theorem full_split_convexification {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (l : List (Fin n)) (hnd : l.Nodup) (heq : l.toFinset = Nprime) :
    IteratedSplit (Poly A b) l = convexHull ℝ (K0Set A b Nprime) := by sorry

end Disjunctive.HigherDim
