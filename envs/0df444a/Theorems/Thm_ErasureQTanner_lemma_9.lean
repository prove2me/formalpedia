-- Prove2me | Theorems.Thm_ErasureQTanner_lemma_9
-- name    : ErasureQTanner.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:14.007863+00:00
-- url     : https://prove2.me/theorems/84e11c07-1dd1-4408-adf5-46d901f19c50
-- title:
--   Lemma 9 — random linear codes on the erasure channel
-- statement:
--   There is a universal constant $a>0$ such that, for $\rho\in(0,1)$ and a uniformly random linear code $C\subseteq\mathbb F_2^n$ of rate $1-\rho$, for every $\varepsilon\in[0,\rho]$,
--   $$\Pr_{C,\,x\sim\rho-\varepsilon}[\mathrm{decode}(C,x)=0]\le2e^{-a\varepsilon^2n}.$$
--   This is Elias's classical fact, the base case of the classical part of the paper.
--
--   Differences from the source:
--   - encoding: rate $1-\rho$, with $\rho\in(0,1)$ → dimension $k$ with $0<k<n$ and $\rho:=1-k/n$; reason: a code of length $n$ has rate $1-\rho$ exactly in this case
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), Lemma 9, p.19

import Mathlib
import Definitions.Def_ErasureQTanner_noisyProb
import Definitions.Def_ErasureQTanner_covered
import Definitions.Def_ErasureQTanner_uniformAvg

set_option autoImplicit false

namespace ErasureQTanner

/-- **Lemma 9** ([Eli55]). Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.19: there is a universal `a > 0` such that for `ρ ∈ (0, 1)` and a
uniformly random linear code `C ⊆ F₂ⁿ` of rate `1 − ρ`, for any `ε ∈ [0, ρ]`,
`Pr_{C, x∼ρ−ε}[decode(C, x) = 0] ≤ 2e^{−aε²n}`.

**Formalization Note.** A rate `1 − ρ` code of length `n` exists exactly when `(1 − ρ)n` is an integer `k`, so the rate is
written through `k`, `ρ := 1 − k/n`, and `ρ ∈ (0, 1)` is `0 < k < n`. -/
theorem lemma_9 : ∃ a : ℝ, 0 < a ∧ ∀ n k : ℕ, 0 < k → k < n → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 - (k : ℝ) / n →
    uniformAvg n k (fun C => noisyProb (1 - (k : ℝ) / n - ε) (decodeFails C)) ≤
      2 * Real.exp (-(a * ε ^ 2 * n)) := by sorry

end ErasureQTanner
