-- Prove2me | Theorems.Thm_CausalFailureRank_lemma_B_1
-- name    : CausalFailureRank.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:07.92023+00:00
-- url     : https://prove2.me/theorems/65435618-1b99-4350-a320-e743a95e8967
-- title:
--   Lemma B.1 — local logarithmic price
-- statement:
--   For the fixed stage-$i$ experiment,
--   $$J_i(t)=A_i\log t\,(1+o(1))\quad(t\to\infty),\qquad 0\le J_i(t)\le t,$$
--   and $J_i(t)=O_i(\log(1+t))$ for all $t\ge0$. Bayes sequential testing with error penalty $t$ thus costs the information weight times $\log t$.
--
--   Differences from the source:
--   - encoding: $1+o(1)$ and $O_i$ → the ratio tends to $1$; an explicit constant $K$; reason: meaning of the symbols
--   - encoding: $J_i(t)$ real → valued in $[0,\infty]$, with $J_i(t)\le t$ giving finiteness, so $0\le J_i$ is automatic; reason: Lean convention
--   - generalization: rational probabilities, fees and risk parameters → real ones; reason: rationality serves only computability, which is not claimed here; the rational case is an instance
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.1, Lemma B.1, p.15

import Mathlib
import Definitions.Def_CausalFailureRank_coefficient
import Definitions.Def_CausalFailureRank_J

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- **Lemma B.1 (Local logarithmic price).** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.1, p.15: "J_i(t) = A_i log t (1 + o(1)) (t → ∞),
0 ≤ J_i(t) ≤ t. Moreover J_i(t) = O_i(log(1 + t)) for all t ≥ 0."

**Formalization Note.** `J` is valued in `ℝ≥0∞`, so `0 ≤ J` is automatic and `J i t ≤ ofReal t` gives its
finiteness. -/
theorem lemma_B_1 (I : Instance N q) (i : Fin N) :
    Tendsto (fun t => (J I i t).toReal / (A I i * Real.log t)) atTop (𝓝 1) ∧
    (∀ t : ℝ, 0 ≤ t → J I i t ≤ ENNReal.ofReal t) ∧
    ∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → J I i t ≤ ENNReal.ofReal (K * Real.log (1 + t)) := by sorry

end CausalFailureRank
