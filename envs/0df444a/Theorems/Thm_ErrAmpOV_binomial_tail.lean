-- Prove2me | Theorems.Thm_ErrAmpOV_binomial_tail
-- name    : ErrAmpOV.binomial_tail
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:53.907031+00:00
-- url     : https://prove2.me/theorems/e9121ecb-1994-43c2-a84b-e842d80e8fde
-- title:
--   Binomial tail display (proof of Theorem 4.3, p.15) — more than half of $\ell$ independent events
-- statement:
--   Let $E_1,\dots,E_\ell$ be independent events in a probability space, each of probability at most $p$ (a real number). Then
--   $$
--   \Pr\bigl[\text{more than }\ell/2\text{ of the events occur}\bigr]\le (2e\,p)^{\ell/2}.
--   $$
--
--   In the amplified circuit, the events are the aborts of the fresh runs in one round. The bound says that a round fails to resolve half of its instances only with probability exponentially small in the number of instances.
--
--   **Formalization Note** The exponent $\ell/2$ is real (`Real.rpow`). For $2ep\ge1$ the right side is at least 1, so no upper bound on $p$ is needed.
--
--   Differences from the source:
--   - generalization: indicator variables that are 1 with probability p(B) (1/10 on p.11), all with the same probability, within an iteration → independent events (iIndepSet) with μ.real (E i) ≤ p, for any real p, on any probability space; reason: probabilities may differ, and no sign condition on p is imposed (for ℓ ≥ 1 the bound forces p ≥ 0; at ℓ = 0 the claim is 0 ≤ 1); the page's case is equal probabilities p ∈ [0,1]
--   - encoding: the chain (e·p·ℓ/(ℓ/2))^{ℓ/2} ≤ (2e·p)^{ℓ/2} → only the outer bound, ≤ (2e·p)^{ℓ/2}; reason: the middle term equals the right side
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), unnumbered display in the proof of Theorem 4.3, p.15; invoked in the proof of Theorem 3.2, p.11, as "the standard Chernoff bounds"

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ErrAmpOV

/-- Binomial tail bound (unnumbered display in the proof of Theorem 4.3, p.15; invoked in the
proof of Theorem 3.2, p.11, as "the standard Chernoff bounds"). Let `E_0, …, E_{ℓ-1}` be
independent events, each of probability at most `p`. Then the probability that more than `ℓ/2`
of them occur is at most `(2e·p)^{ℓ/2}`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
proof of Theorem 4.3, p.15 (the display
`(e·p(B)·ℓ_k/(ℓ_k/2))^{ℓ_k/2} ≤ (2e·p(B))^{ℓ_k/2}`); proof of Theorem 3.2, p.11.

**Formalization Note.** The events need not have equal probabilities; each has probability
`≤ p` (so `p ≥ 0` as soon as `ℓ ≥ 1`; at `ℓ = 0` both sides are `0` and `1` for every real `p`,
so no sign hypothesis on `p` is needed). No upper bound on `p` is assumed: for `2e·p ≥ 1` the right side is at least
`1`. The number of events that occur is `Set.ncard {i | ω ∈ E i}`. The exponent `ℓ/2` is real (`Real.rpow`). "More than `ℓ/2`" is as printed. -/
theorem binomial_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℓ : ℕ) (E : Fin ℓ → Set Ω) (hE : ∀ i, MeasurableSet (E i)) (hind : iIndepSet E μ)
    (p : ℝ) (hle : ∀ i, μ.real (E i) ≤ p) :
    μ.real {ω | (ℓ : ℝ) / 2 < (({i : Fin ℓ | ω ∈ E i}.ncard : ℕ) : ℝ)} ≤
      (2 * Real.exp 1 * p) ^ ((ℓ : ℝ) / 2) := by sorry

end ErrAmpOV
