-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_sherali_adams_subset_iterated_split
-- name    : Disjunctive.HigherDim.sherali_adams_subset_iterated_split
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:41:49.109265+00:00
-- url     : https://prove2.me/theorems/57229d57-d02b-4471-a0c2-dfffbee30aa5
-- title:
--   Theorem 7.7 — Kt is contained in the split hull over any same-size subset
-- statement:
--   This is Theorem 7.7 of Balas's *Disjunctive Programming* — **not extracted by
--   `statements.jsonl`'s regex pass**; verified directly against the PDF and added here manually,
--   since the book names it explicitly as the second of Theorem 7.6's two proof ingredients.
--
--   $$
--   K_t \subseteq P_{1,\dots,t}(K), \quad t = 1,\dots,p.
--   $$
--
--   More precisely (matching the book's own proof, which fixes an arbitrary valid inequality of
--   $P_{1,\dots,t}(K)$ and re-derives it from $(NL_t)$'s rows by induction on $t$), this item states
--   the fact for an arbitrary $t$-subset $S \subseteq N'$ in place of the literal prefix
--   $\{1,\dots,t\}$: $K_t \subseteq \mathrm{conv}(K \cap \bigcap_{j \in S}\{x_j \in
--   \{0,1\}\})$, which specializes to the book's own statement when $S = \{1,\dots,t\}$ and is
--   what the goal theorem's proof actually needs (it is applied at $S = N'$, $t = |N'|$).
--
--   **Formalization Note.** The book's proof is a genuine induction re-deriving every valid inequality
--   of $P_{1,\dots,t}(K)$ from a nonnegative combination of $(NL_t)$'s own rows — a real argument, not
--   a restatement — so this item is included as a milestone with its own content, not merely assumed;
--   the `by sorry` proof obligation is exactly this induction.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 95, Theorem 7.7

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts

namespace Disjunctive.HigherDim

/-- Theorem 7.7 (Balas §7.3, p. 96, [112]): the Sherali-Adams `t`-th level lift `K_t`, restricted
to any `t`-subset `S` of the 0-1 index set `N'`, is contained in the convex hull of imposing 0-1
on all of `S` at once. -/
theorem sherali_adams_subset_iterated_split {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (Nprime S : Finset (Fin n)) (t : ℕ) (hS : S ⊆ Nprime) (hcard : S.card = t) :
    KtSet A b Nprime t ⊆ convexHull ℝ (Poly A b ∩ ⋂ j ∈ S, ZeroOneSet j) := by sorry

end Disjunctive.HigherDim
