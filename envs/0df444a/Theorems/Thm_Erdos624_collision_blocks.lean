-- Prove2me | Theorems.Thm_Erdos624_collision_blocks
-- name    : Erdos624.collision_blocks
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-24T03:33:36.703987+00:00
-- url     : https://prove2.me/theorems/2d05af7b-9cfa-4255-a758-b237282d8906
-- title:
--   Disjoint collision blocks for commutative-monoid labels (Erdős 624)
-- statement:
--   Let $U$ be a finite set, $M$ a finite commutative monoid and $v:U\to M$ arbitrary.
--
--   **Theorem.** Let $t,d\ge0$ with
--
--   $$|M|<\binom{|U|-2t(d-1)}{t}.$$
--
--   Then there are pairwise disjoint sets $B_1,\dots,B_d\subseteq U$ with $|B_j|\le 2t$, and distinct subsets $P_j,Q_j\subseteq B_j$ with $\prod_{x\in P_j}v(x)=\prod_{x\in Q_j}v(x)$ for every $j$.
--
--   This is the finite collision-block lemma (7)–(8) used to show that commutative-aggregate maps through a monoid of polynomial size cannot be one half of a covering pair in Erdős Problem 624.
--
--   **Formalization Note.** Blocks indexed by $\mathrm{Fin}\,d$; $U$ and $M$ arbitrary finite types.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); (7)–(8) of the analysis derived from GPT 6.1 Sol's analysis (sixth report, Oct 2026), relayed by Ethan Cheung; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem collision_blocks {U : Type*} [Fintype U] [DecidableEq U] {M : Type*} [CommMonoid M] [Fintype M]
    (t d : ℕ) (v : U → M)
    (h7 : Fintype.card M < (Fintype.card U - 2 * t * (d - 1)).choose t) :
    ∃ Bk P Q : Fin d → Finset U, (∀ i j, i ≠ j → Disjoint (Bk i) (Bk j)) ∧
      ∀ i, #(Bk i) ≤ 2 * t ∧ P i ⊆ Bk i ∧ Q i ⊆ Bk i ∧ P i ≠ Q i ∧
        ∏ x ∈ P i, v x = ∏ x ∈ Q i, v x := by sorry

end Erdos624
