-- Prove2me | Theorems.Thm_AgnHalfMem_theorem_4_10
-- name    : AgnHalfMem.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:15:36.111458+00:00
-- url     : https://prove2.me/theorems/0a598ead-911a-49e9-a459-6bc2ef5ed404
-- title:
--   Theorem 4.10 — under every product marginal $\mu^{\otimes d}$, agnostic learning of halfspaces needs $\Omega(d/\varepsilon^2)$ bits or $2^{\Omega(1/\varepsilon^2)}$ samples
-- statement:
--   There are constants $C>0$, $\varepsilon_0\in(0,1)$ and $c>0$ such that the following holds. Let $\mu$ be any probability distribution on $\mathbb R$ with finite non-zero variance $\sigma^2$, and let $L=L_\mu\ge1$ be its half-variance radius. Let $d\ge1$ and
--   $$
--   \frac{CL}{\sqrt d}\ \le\ \varepsilon\ \le\ \varepsilon_0 .
--   $$
--   Then no randomized streaming algorithm that uses at most $c\,d/\varepsilon^2$ bits of memory (at most $2^{c d/\varepsilon^2}$ states) and at most $2^{c/\varepsilon^2}$ samples agnostically learns the homogeneous halfspaces $\mathcal H_d$ under marginal $\mu^{\otimes d}$ to excess error $\varepsilon$: for some distribution $D$ on $\mathbb R^d\times\{-1,1\}$ with $X$-marginal $\mu^{\otimes d}$, the algorithm outputs $f$ with $\mathrm{err}(f,D)\le\mathrm{OPT}_{\mathcal H_d}(D)+\varepsilon$ with probability less than $0.9$.
--
--   Equivalently, any streaming algorithm that agnostically learns halfspaces under $\mu^{\otimes d}$ to excess error $\varepsilon$ requires either $\Omega(d/\varepsilon^2)$ bits of memory or $2^{\Omega(1/\varepsilon^2)}$ samples, while $O(d/\varepsilon^2)$ samples suffice without a memory limit. This is the paper's main theorem; the Gaussian and sparse Bernoulli marginals are special cases.
--
--   Differences from the source:
--   - generalization: "Let µ … There exist constants 0 < C < ∞ and ε₀ ∈ (0,1)" (constants after µ) and Ω-constants → C, ε₀ and c chosen before µ, d, ε and the algorithm; reason: the proof's constants are universal (p.17: "c, c′ > 0 are universal constants"); the uniform statement specializes to the printed order
--   - encoding: "requires either Ω(d/ε²) bits of memory or 2^{Ω(1/ε²)} samples" → no algorithm with card S ≤ 2^{c·d/ε²} and (T:ℝ) ≤ 2^{c/ε²} learns; one constant c for both; reason: b bits of memory is at most 2^b states; Ω means some positive constant and two constants reduce to their minimum
--   - generalization: "any streaming algorithm" (App. B: deterministic branching programs WLOG) → every seeded family of Definition B.1 programs on any seed space Ω with seed law P; reason: deterministic algorithms are the case of a one-point seed space
--   - encoding: probabilities over the algorithm's randomness and the samples → IsMeasurableAlg A (joint measurability in seed and sample); reason: a probability presupposes measurable events; without it a non-measurable partition of the seed space lets a zero-memory algorithm succeed with outer probability 1
--   - encoding: labels in {−1,1}, x ∈ ℝ^d, ‖w‖₂ = 1, µ^{⊗d}, "finite non-zero variance", "with probability at least 0.9" → Bool with true ↔ +1, Fin d → ℝ, Σ w_i² = 1, Measure.pi, IsProbabilityMeasure ∧ MemLp id 2 ∧ 0 < variance, ofReal 0.9 ≤ product measure of the success set; reason: Lean conventions; same instances
--   - encoding: d unrestricted → 0 < d; reason: CL/√d is undefined at d = 0; Lean's x/0 = 0 would admit every ε
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Theorem 4.10, p.17 (proof pp.17–18)

import Mathlib
import Definitions.Def_AgnHalfMem_halfspace
import Definitions.Def_AgnHalfMem_AgnLearnsUnder
import Definitions.Def_AgnHalfMem_halfVarRadius

open MeasureTheory ProbabilityTheory

universe u v

namespace AgnHalfMem

/-- **Theorem 4.10 (agnostically learning halfspaces under general i.i.d. product marginals).**
S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027
submission (manuscript, PDF sha256 386bc9b3…43f84d5), Theorem 4.10, p.17: "Let µ be any
distribution with finite non-zero variance σ² > 0. Let 1 ≤ L be its half-variance radius. There
exist constants 0 < C < ∞ and ε₀ ∈ (0, 1) such that for all CL/√d ≤ ε ≤ ε₀, any streaming
algorithm that agnostically learns halfspaces under marginal µ^{⊗d} to excess error ε requires
either Ω(d/ε²) bits of memory or 2^{Ω(1/ε²)} samples."

There are constants `C > 0`, `ε₀ ∈ (0, 1)` and `c > 0` such that for every probability measure
`μ` on `ℝ` with finite non-zero variance, every `d ≥ 1` and every `ε` with
`C L_μ/√d ≤ ε ≤ ε₀`, no randomized streaming algorithm with at most `2^{c d/ε²}` memory states
(i.e. `c d/ε²` bits) and at most `2^{c/ε²}` samples agnostically learns `H_d` under `μ^{⊗d}` to
excess error `ε`.

**Formalization Note.** The constants `C, ε₀, c` are chosen before `μ` (the proof's constants are
universal, p.17); `Ω(·)` is one explicit constant `c` for both resources. Memory of `b` bits is
`Fintype.card S ≤ 2^b`. Algorithms are seeded families of Definition B.1 programs on any seed
space, jointly measurable (`IsMeasurableAlg`). `0 < d` excludes the undefined `CL/√0`. -/
theorem theorem_4_10 :
    ∃ C ε₀ c : ℝ, 0 < C ∧ 0 < ε₀ ∧ ε₀ < 1 ∧ 0 < c ∧
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ → MemLp id 2 μ → 0 < variance id μ →
      ∀ (d : ℕ), 0 < d → ∀ ε : ℝ, C * halfVarRadius μ / Real.sqrt d ≤ ε → ε ≤ ε₀ →
      ∀ (Ω : Type u) (S : Type v) [MeasurableSpace Ω] [Fintype S] (T : ℕ)
        (A : StreamAlg Ω S (Fin d → ℝ) T) (P : Measure Ω), IsProbabilityMeasure P →
        IsMeasurableAlg A →
        (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ (c * d / ε ^ 2) → (T : ℝ) ≤ (2 : ℝ) ^ (c / ε ^ 2) →
        ¬ AgnLearnsUnder (Measure.pi fun _ : Fin d => μ) (halfspaces d) ε A P := by sorry

end AgnHalfMem
