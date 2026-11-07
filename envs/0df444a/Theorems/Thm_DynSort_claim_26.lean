-- Prove2me | Theorems.Thm_DynSort_claim_26
-- name    : DynSort.claim_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:02.574307+00:00
-- url     : https://prove2.me/theorems/8d511ea3-6d5f-46a9-976c-966eed06fbc9
-- title:
--   Claim 26 — ReBuild recourse is $O(dM)$ after $M$ SwapHole calls
-- statement:
--   There is a constant $C$ such that, for every $n$ and every run from the initial A-DST of level $d=1+\lceil\log_2 n\rceil$, at every point of the execution the total recourse of the ReBuild operations triggered so far is at most
--   $$C\,d\,M,$$
--   where $M$ is the number of SwapHole calls made so far (inside DSTs and between components).
--
--   **Formalization Note** ReBuild runs only inside SwapHole, so both quantities change only at SwapHole calls; the bound is stated at every such call, which covers every point of the execution.
--
--   Differences from the source:
--   - encoding: at any point during the execution, O(dM) → after every SwapHole call of every run from the initial A-DST (the log of the counters), ∃ C : ℕ before n; reason: the two counters change only at SwapHole calls, so these are all the points at which the bound can change
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 26, p.25 (PDF p.27); proof pp.55–56 (PDF pp.57–58)

import Mathlib
import Definitions.Def_DynSort_ADST

namespace DynSort

/-- **Claim 26**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §5.2, p.25 (PDF p.27; proof pp.55–56): "At any point during the
execution of a d-level A-DST, let M denote the number of SwapHole calls made so far. Then, the
total recourse incurred by the resulting ReBuild operations is O(dM)."

**Formalization Note.** ReBuild runs only inside SwapHole, so the ReBuild recourse and `M` change
only at SwapHole calls; `swapLog` records both after every call, internal and between components.
One constant `C` serves every `n` and every run from the initial A-DST of level
`d = (initElt n).d`: every recorded point satisfies `rebuildMoves ≤ C·d·M`. -/
theorem claim_26 :
    ∃ C : ℕ, ∀ (n : ℕ) (ps : List (Elt × Elt)), (initElt n).ValidRun ps →
      ∀ p ∈ ((initElt n).runFrom ps).ctr.swapLog, p.1 ≤ C * (initElt n).d * p.2 := by sorry

end DynSort
