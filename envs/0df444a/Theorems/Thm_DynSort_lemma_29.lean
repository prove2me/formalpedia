-- Prove2me | Theorems.Thm_DynSort_lemma_29
-- name    : DynSort.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:39.735936+00:00
-- url     : https://prove2.me/theorems/a104f7c0-3c7b-41ef-ab1b-962de482c520
-- title:
--   Lemma 29 — Delete costs $O(i^4)$ amortized recourse
-- statement:
--   There is a constant $C$ such that, for every $n$ and every run of $K$ deletion–insertion pairs from the initial A-DST of $n$ virtual elements, of level $i=1+\lceil\log_2 n\rceil$, the total recourse of the $K$ Delete operations (their own element movements plus the recourse of the ReBuild operations they trigger) is at most
--   $$C\,i^4\,K .$$
--
--   Insert and Re-Sort are counted separately, as in the assembly of §5.5.
--
--   Differences from the source:
--   - encoding: the amortized recourse of Delete on a level-i A-DST is O(i⁴) → ∃ C : ℕ before n; for every run of K pairs from the initial A-DST of level i, Delete's moves plus ReBuild recourse ≤ C·i⁴·K; reason: amortized recourse is the total divided by the number of updates (p.6)
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Lemma 29, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_DynSort_ADST

namespace DynSort

/-- **Lemma 29**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §5.3, p.26 (PDF p.28): "The amortized recourse of Delete on a level-i
A-DST is O(i⁴)."

**Formalization Note.** One constant `C` for every `n` and every run of `K` deletion–insertion
pairs from the initial A-DST of level `i = (initElt n).d`: the recourse of the `K` Delete
operations, their own moves plus the recourse of the ReBuild calls they trigger, is at most
`C·i⁴·K`. Insert and Re-Sort are counted separately, as in §5.5. -/
theorem lemma_29 :
    ∃ C : ℕ, ∀ (n : ℕ) (ps : List (Elt × Elt)), (initElt n).ValidRun ps →
      ((initElt n).runFrom ps).ctr.moves + ((initElt n).runFrom ps).ctr.rebuildMoves ≤
        C * (initElt n).d ^ 4 * ps.length := by sorry

end DynSort
