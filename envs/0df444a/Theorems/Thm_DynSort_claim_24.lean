-- Prove2me | Theorems.Thm_DynSort_claim_24
-- name    : DynSort.claim_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:27.54779+00:00
-- url     : https://prove2.me/theorems/10e1a727-d9b8-415b-be4e-c1a5323f8f1d
-- title:
--   Claim 24 — Re-Sort costs $O(i)$ amortized recourse per update
-- statement:
--   There is a constant $C$ such that, for every $n$ and every run of $K$ deletion–insertion pairs from the initial A-DST of $n$ virtual elements, whose level is $d=1+\lceil\log_2 n\rceil$, the total recourse of all Re-Sort operations is at most
--   $$C\,d\,K .$$
--
--   Differences from the source:
--   - encoding: for a level-i A-DST, amortized recourse O(i) per update → ∃ C : ℕ before n; for every run of K pairs from the initial A-DST of level d, total Re-Sort recourse ≤ C·d·K; reason: amortized recourse is the total over the updates divided by their number (p.6); runs start from the initialization of p.6
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 24, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_DynSort_ADST

namespace DynSort

/-- **Claim 24**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §5.2, p.24 (PDF p.26): "For a level-i A-DST, the amortized recourse
incurred by Re-Sort is O(i) per update."

**Formalization Note.** One constant `C` for every `n` and every run of `K` deletion–insertion
pairs from the initial A-DST of `n` virtual elements, whose level is `d = (initElt n).d`
`= 1 + ⌈log₂ n⌉`: the total Re-Sort recourse is at most `C·d·K`, with no additive term. -/
theorem claim_24 :
    ∃ C : ℕ, ∀ (n : ℕ) (ps : List (Elt × Elt)), (initElt n).ValidRun ps →
      ((initElt n).runFrom ps).resortMoves ≤ C * (initElt n).d * ps.length := by sorry

end DynSort
