-- Prove2me | Theorems.Thm_BlockCycleRotation_heilbronn_bijection
-- name    : BlockCycleRotation.heilbronn_bijection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:29.232372+00:00
-- url     : https://prove2.me/theorems/661e5da8-d99c-427d-9aec-2b8ab420f364
-- title:
--   Heilbronn's bijection between normalised expansions and coprime pairs
-- statement:
--   For a list $l=(c_1,\dots,c_r)$ of positive integers let $K(l)$ denote its continuant, the numerator of the continued fraction $[c_1;c_2,\dots,c_r]$, and call $l$ **normalised** if it is nonempty, has positive entries, and its first entry is at least $2$. Write $\Phi(l) = (K(l),\, K(l_{\mathrm{dropLast}}))$ and let $\operatorname{cf}$ be the expansion produced by the Euclidean algorithm.
--
--   The theorem is a conjunction of two round-trip statements.
--
--   1. For every normalised $l$: $\operatorname{cf}(\Phi(l)) = l$.
--   2. For every coprime pair $a > a' \ge 1$: $\operatorname{cf}(a,a')$ is normalised, and $\Phi$ of it is $(a,a')$.
--
--   Together these say that $\operatorname{cf}$ and $\Phi$ invert one another where both are applied. They do **not** on their own assert that $\Phi$ maps normalised lists into the coprime pairs — that $K(l_{\mathrm{dropLast}}) < K(l)$, that it is at least $1$, and that the two are coprime. That forward direction is the separate result `heilbronn_forward`; only in conjunction with it do these equations amount to a bijection between normalised expansions and coprime pairs $a > a' \ge 1$.
--
--   This correspondence, due to Heilbronn (1969), is what §4 uses to convert the sum of remainder sums over all shifts into a count of lattice points indexed by coprime pairs.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4, Heilbronn 1969. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L379-L394

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.heilbronn_bijection :
    (∀ l : List ℕ, l ≠ [] → (∀ c ∈ l, 1 ≤ c) → (∀ x ∈ l.head?, 2 ≤ x) →
        cf (K l) (K l.dropLast) = l)
      ∧ (∀ a a' : ℕ, 1 ≤ a' → a' < a → Nat.gcd a a' = 1 →
        (cf a a' ≠ [] ∧ (∀ c ∈ cf a a', 1 ≤ c) ∧ (∀ x ∈ (cf a a').head?, 2 ≤ x))
          ∧ K (cf a a') = a ∧ K (cf a a').dropLast = a') := by sorry
