-- Prove2me | Theorems.Thm_AggCG_Supplement_theorem_3_3
-- name    : AggCG.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:27:29.182345+00:00
-- url     : https://prove2.me/theorems/dcf530db-06f9-4114-98e7-b149b348ca8a
-- title:
--   Theorem 3.3 — smoothed power-mean linkage path complexity
-- statement:
--   Let $S$ contain $n\ge2$ points, and draw its primitive unordered-pair distances independently from $[1,2]$, each with density at most $\kappa$. For any fixed deterministic tie rule and finite union of intervals $\Theta\subseteq\mathbb R$, let $K(S;\Theta)$ count finite exponents in $\Theta$ at which the complete power-mean linkage hierarchy changes. Then
--
--   $$
--   \mathbb E K(S;\Theta)\le 2\kappa {n\choose2}(n-1)n^2\int_\Theta
--   \min\!\left\{\frac{(\log2)^2}{8},\frac{2\log n}{\alpha^2}\right\}\,d\alpha.
--   $$
--
--   Consequently, for one absolute constant $C$, $\mathbb E K(S;\mathbb R)\le C\kappa n^5\sqrt{\log n}$.
--
--   Differences from the source:
--   - encoding: the source counts a finite integer-valued random variable and uses the continuous value $(\log 2)^2/8$ at $\alpha=0$ → Lean counts change points in $\mathbb N\cup\{\infty\}$, takes a lower Lebesgue integral, and assigns the integrand value $0$ at the singleton $\alpha=0$; reason: this prevents an infinite change set from defaulting to zero, and changing one point leaves the integral unchanged
-- source:
--   Sharma, Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem 3.3, p.4, PDF p.5

import Mathlib
import Definitions.Def_AggCG_Supplement_linkageHierarchy
import Definitions.Def_AggCG_Supplement_changePoints
import Definitions.Def_AggCG_Supplement_BoundedDensityOn

namespace AggCG.Supplement

open MeasureTheory

/-- **Theorem 3.3** (Smoothed linkage path complexity; Sharma, *Computational Complexity of Data-Driven
Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission
(manuscript sha256 f7ea0248…), p.4, PDF p.5). Let `S` have `n ≥ 2` points and draw its primitive
unordered-pair distances `D_{ij}` (`i < j`) independently, each with a law on `[1, 2]` of density at most
`κ`. For every fixed deterministic tie rule and every finite union of intervals `Θ ⊆ ℝ`, the number
`K(S; Θ)` of finite exponents `α ∈ Θ` at which the complete power-mean linkage hierarchy changes satisfies
`E K(S; Θ) ≤ 2κ C(n,2)(n − 1)n² ∫_Θ min{(log 2)²/8, 2 log n/α²} dα`; consequently, with one absolute
constant `C`, `E K(S; ℝ) ≤ C κ n⁵ √(log n)`.

**Formalization Note** The expectation is the lower Lebesgue integral of the `ℕ∞`-valued count, and
almost-everywhere measurability of the count is part of the claim, so the bound is on the actual
expectation. The integrand is `0` at `α = 0` in Lean instead of its continuous value `(log 2)²/8`, which
changes the integral on a null set only. -/
theorem theorem_3_3 :
    (∀ (n : ℕ), 2 ≤ n → ∀ (κ : ℝ) (ν : {p : Fin n × Fin n // p.1 < p.2} → Measure ℝ)
      [∀ p, IsProbabilityMeasure (ν p)], (∀ p, BoundedDensityOn (ν p) κ 1 2) →
      ∀ (tie : TieRule) (Θ : Set ℝ),
        (∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧ Θ = ⋃ I ∈ s, I) →
        AEMeasurable (fun D => ((changeCount (fun α : ℝ => linkageHierarchy tie (symDist D) (α : EReal))
            Θ : ℕ∞) : ENNReal)) (Measure.pi ν) ∧
        ∫⁻ D, ((changeCount (fun α : ℝ => linkageHierarchy tie (symDist D) (α : EReal)) Θ : ℕ∞) :
            ENNReal) ∂(Measure.pi ν) ≤
          ENNReal.ofReal (2 * κ * (n.choose 2 : ℝ) * ((n : ℝ) - 1) * (n : ℝ) ^ 2) *
            ∫⁻ α in Θ, ENNReal.ofReal (min (Real.log 2 ^ 2 / 8) (2 * Real.log n / α ^ 2))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (κ : ℝ) (ν : {p : Fin n × Fin n // p.1 < p.2} → Measure ℝ)
      [∀ p, IsProbabilityMeasure (ν p)], (∀ p, BoundedDensityOn (ν p) κ 1 2) → ∀ tie : TieRule,
        ∫⁻ D, ((changeCount (fun α : ℝ => linkageHierarchy tie (symDist D) (α : EReal)) Set.univ : ℕ∞) :
            ENNReal) ∂(Measure.pi ν) ≤
          ENNReal.ofReal (C * κ * (n : ℝ) ^ 5 * Real.sqrt (Real.log n))) := by sorry

end AggCG.Supplement
