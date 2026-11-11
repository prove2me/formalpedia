-- Prove2me | Theorems.Thm_AgnHalfMem_lemma_4_5
-- name    : AgnHalfMem.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:07.060991+00:00
-- url     : https://prove2.me/theorems/e941b00f-d74c-41a8-97e9-4f6bb96bfe97
-- title:
--   Lemma 4.5 — $(\epsilon,\eta)$-orthogonal columns form an $L_2$-extractor
-- statement:
--   There are constants $a>0$ and $K_0$ such that the following holds. Let $(X,\mu)$ be a probability space and let $f_1,\dots,f_m:X\to[-1,1]$ be measurable and $(\epsilon,\eta)$-orthogonal with respect to $\mu$, where $\epsilon,\eta>0$ and
--   $$
--   L:=\min\{\log_2(1/\eta),\ \log_2(1/\epsilon)\}\ \ge K_0 .
--   $$
--   Then the matrix $M'(x,i)=f_i(x)$ on $X\times[m]$ is a $(k,\ell)$-$L_2$-extractor with error $2^{-r}$ for $\mu$, where
--   $$
--   \ell=a\log_2(1/\eta),\qquad k=r=a\,L .
--   $$
--
--   Lemma 4.5 extends [GRT18, Lemma 5.8] to infinite feature spaces and real-valued matrices; it is how near-orthogonality of the sine family turns into the extractor property.
--
--   Differences from the source:
--   - encoding: ℓ = Ω(log 1/η), k, r = Ω(min{log 1/η, log 1/ϵ}) → one constant a: ℓ = a·log₂(1/η), k = r = a·min{log₂(1/η), log₂(1/ϵ)}; reason: Ω means some positive constant; constants reduce to their minimum; the proof's logarithms are base 2
--   - reading: no explicit size condition in the statement; the proof's last step "holds for sufficiently large L" (p.12) → K₀ ≤ min{log₂(1/η), log₂(1/ϵ)}; reason: the asymptotic statement is meant for large L; for η = ϵ = 1 the conclusion fails
--   - encoding: columns f_i : X → [−1,1] → Measurable (f i) and values in Set.Icc (−1) 1; reason: expectations under µ presuppose measurability
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Lemma 4.5, p.11 (proof pp.11–12)

import Mathlib
import Definitions.Def_AgnHalfMem_IsOrthogonalFamily
import Definitions.Def_AgnHalfMem_IsL2Extractor

open MeasureTheory

universe u

namespace AgnHalfMem

/-- **Lemma 4.5 (almost orthogonality implies the extractor property).** S. Garg, T. Jadhav,
*Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript,
PDF sha256 386bc9b3…43f84d5), Lemma 4.5, p.11: "Let M′ : X × [m] → [−1, 1] be a matrix whose
columns are functions f₁, …, f_m : X → [−1, 1]. Suppose that the functions are (ϵ,η) orthogonal.
Then M′ is a (k, ℓ)-L2-extractor with error 2^{−r} with respect to distribution µ, for some
ℓ = Ω(log 1/η), k, r = Ω(min{log 1/η, log 1/ϵ})."

There are constants `a > 0` and `K₀` such that for every probability space `(X, μ)` and every
`(ϵ, η)`-orthogonal family `f₁, …, f_m : X → [−1, 1]` with
`min{log₂(1/η), log₂(1/ϵ)} ≥ K₀`, the matrix `M′(x, i) = f_i(x)` is a `(k, ℓ)`-L2-extractor
with error `2^{−r}`, where `ℓ = a log₂(1/η)` and `k = r = a min{log₂(1/η), log₂(1/ϵ)}`.

**Formalization Note.** "Sufficiently large L" in the proof (p.12) is the threshold `K₀` on
`L = min{log₂(1/η), log₂(1/ϵ)}`; logarithms are base 2 (the proof's `A = log₂ 1/η`). The columns
are measurable (expectations under `μ` presuppose it). -/
theorem lemma_4_5 :
    ∃ a K₀ : ℝ, 0 < a ∧ 0 < K₀ ∧
      ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
      ∀ (m : ℕ) (f : Fin m → X → ℝ), (∀ i, Measurable (f i)) →
        (∀ i x, f i x ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ ϵ η : ℝ, 0 < ϵ → 0 < η → IsOrthogonalFamily μ f ϵ η →
        K₀ ≤ min (Real.logb 2 (1 / η)) (Real.logb 2 (1 / ϵ)) →
        IsL2Extractor μ (fun x i => f i x)
          (a * min (Real.logb 2 (1 / η)) (Real.logb 2 (1 / ϵ)))
          (a * Real.logb 2 (1 / η))
          (a * min (Real.logb 2 (1 / η)) (Real.logb 2 (1 / ϵ))) := by sorry

end AgnHalfMem
