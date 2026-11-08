-- Prove2me | Theorems.Thm_CausalFailureRank_eq_22
-- name    : CausalFailureRank.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:15:55.999568+00:00
-- url     : https://prove2.me/theorems/5ac8e4c8-2451-4592-9618-48d13931dd40
-- title:
--   Eq. (22) — asymptotics of the local targets
-- statement:
--   For each fixed $j\ge1$, as $r\to0^+$,
--   $$\log\frac1{p_j(r)}=\ell_{j+1}(1/r)+O_j(1),\qquad p_j(r)=O_j\big(1/\ell_j(1/r)\big).$$
--   These targets make the error branch's cost negligible while keeping the local cost at the next logarithmic layer.
--
--   Differences from the source:
--   - encoding: $O_j$ → a constant chosen after $j$, with an eventual bound as $r\to0^+$; reason: meaning of the symbol
--   - encoding: $p_j(r)=O_j(1/\ell_j(1/r))$ → $|p_j(r)\,\ell_j(1/r)|$ bounded; reason: $\ell_j(1/r)>0$ eventually, so they are the same
--   - generalization: rational $r$ with integer comparisons → real $r$ with $\log_2$; reason: rational $r$ is an instance
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.4, eq. (22), p.17

import Mathlib
import Definitions.Def_CausalFailureRank_coefficient
import Definitions.Def_CausalFailureRank_refController

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- **Eq. (22).** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.4, p.17: "For each fixed j ≥ 1, log(1/p_j(r)) = ℓ_{j+1}(1/r) + O_j(1),
p_j(r) = O_j(1/ℓ_j(1/r))."

**Formalization Note.** Asymptotics as `r → 0⁺`, with the constants chosen after `j`. -/
theorem eq_22 (j : ℕ) (hj : 1 ≤ j) :
    (∃ K : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), |Real.log (1 / pj j r) - iterLog (j + 1) (1 / r)| ≤ K) ∧
    ∃ K : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), |pj j r * iterLog j (1 / r)| ≤ K := by sorry

end CausalFailureRank
