-- Prove2me | Theorems.Thm_EntropyLocalCoord_Leader_theorem_4_2
-- name    : EntropyLocalCoord.Leader.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:43.911543+00:00
-- url     : https://prove2.me/theorems/b1487785-1d90-4193-940b-d38deec3cd87
-- title:
--   Theorem 4.2 ([KT02, AS19]) — grand coupling with $P[L_i\ne L_j]\le 2\|\mu_i-\mu_j\|_{TV}/(1+\|\mu_i-\mu_j\|_{TV})$
-- statement:
--   Let $(\mu_i)_{i\in\iota}$ be a finite or countable family of probability measures on a common finite set $K$. Then there exist a probability space and random variables $(L_i)_{i\in\iota}$ with values in $K$ such that $L_i\sim\mu_i$ for every $i$ and, for every pair $i,j$,
--
--   $$P[L_i\ne L_j]\le\frac{2\|\mu_i-\mu_j\|_{TV}}{1+\|\mu_i-\mu_j\|_{TV}}\le2\|\mu_i-\mu_j\|_{TV}.$$
--
--   All pairs of the family are controlled by one coupling, at a cost of at most a factor $2$ over the optimal coupling of a single pair.
--
--   Differences from the source:
--   - encoding: probability measures $\mu_i$ on a finite set $K$ and $L_i\sim\mu_i$ → nonnegative real vectors of sum 1, with $P(L_i=a)=\mu_i(a)$ for each $a$, on a type $K$ with measurable singletons; reason: on a finite set these say the same thing
--   - encoding: a finite or countable family and an unspecified probability space → a countable index type and a sample space in Lean's universe `Type`; reason: `Countable` covers finite and countably infinite families; the source fixes no universe
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272, Theorem 4.2, p. 11 (citing Kleinberg–Tardos 2002 and Angel–Spinka 2019).

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Information

open MeasureTheory

namespace EntropyLocalCoord.Leader

/-- Theorem 4.2 ([KT02, AS19]), p. 11: a finite or countable family `(μ_i)` of probability
measures on a common finite set `K` has a coupling `(L_i)` with `L_i ∼ μ_i` for every `i` and, for
every pair `i, j`,
`P[L_i ≠ L_j] ≤ 2‖μ_i - μ_j‖_TV / (1 + ‖μ_i - μ_j‖_TV) ≤ 2‖μ_i - μ_j‖_TV`. -/
theorem theorem_4_2 {ι K : Type} [Countable ι] [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (μ : ι → K → ℝ) (hμ0 : ∀ i a, 0 ≤ μ i a)
    (hμ1 : ∀ i, ∑ a, μ i a = 1) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (L : ι → Ω → K),
      (∀ i, Measurable (L i)) ∧
      (∀ i a, P.real (L i ⁻¹' {a}) = μ i a) ∧
      ∀ i j,
        P.real {ω | L i ω ≠ L j ω} ≤
            2 * tvNorm (fun a => μ i a - μ j a) / (1 + tvNorm (fun a => μ i a - μ j a)) ∧
          2 * tvNorm (fun a => μ i a - μ j a) / (1 + tvNorm (fun a => μ i a - μ j a)) ≤
            2 * tvNorm (fun a => μ i a - μ j a) := by sorry

end EntropyLocalCoord.Leader
