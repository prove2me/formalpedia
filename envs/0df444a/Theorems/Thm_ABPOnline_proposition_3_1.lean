-- Prove2me | Theorems.Thm_ABPOnline_proposition_3_1
-- name    : ABPOnline.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:33.071067+00:00
-- url     : https://prove2.me/theorems/a2a2895c-9c59-4f9f-90f2-64152092087a
-- title:
--   Proposition 3.1 — Brownian limit of a successful online algorithm
-- statement:
--   Suppose $M_N/N\to\alpha\in(0,\infty)$ and a sequence of deterministic online algorithms satisfies
--   $$
--   \mathbb P\Big(\min_{1\le i\le M}X_{N,i}\ge\kappa\Big)\longrightarrow1 .
--   $$
--   Then there exist a filtered probability space with filtration $\mathcal G$, a $\mathcal G$-Brownian motion $B$, and a $\mathcal G$-progressively measurable process $a$ such that
--   $$
--   B_1+\int_0^1a_t\,dt\ge\kappa\ \text{a.s.},\qquad \mathbb Ea_t^2\le\frac{2}{\pi\alpha}\ \text{for a.e. }t\in[0,1].
--   $$
--
--   Following a uniformly chosen row, this is the Brownian scaling limit behind the impossibility direction of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: M/N → α (every integer sequence M_N) → ∀ Mseq : ℕ → ℕ with (Mseq N : ℝ)/N → α; reason: the same; (Mseq N)/N is 0 at N = 0, which does not affect the limit
--   - encoding: σ_k ∈ {−1,+1} F^G_k-measurable, columns g_1, …, g_N → σ k a ±1-valued Borel function of the matrix, equal on matrices that agree in columns 0, …, k; columns indexed from 0; reason: equivalent on the canonical space of the Gaussian matrix
--   - encoding: there exist a filtered probability space, G, B, a → ∃ Ω : Type with a σ-algebra, a probability measure, a filtration indexed by t ≥ 0, B with IsBrownianWrt (Brownian on [0,1], adapted, independent future increments on [0,1]) and a progressive a; reason: the same objects; only [0, 1] is constrained
--   - encoding: E a²_t ≤ 2/(πα) → ∫⁻ ω, ‖a_t(ω)‖² ≤ ENNReal.ofReal(2/(πα)) for a.e. t ∈ [0, 1]; reason: the second moment as a lower integral; no junk value
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Proposition 3.1, (12), p.9 (PDF p.10); proof in Appendix A, pp.30–32

import Mathlib
import Definitions.Def_ABPOnline_IsOnlineAlg
import Definitions.Def_ABPOnline_IsBrownianWrt
import Definitions.Def_ABPOnline_Estar

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ABPOnline

/-- **Proposition 3.1** (arXiv:2609.02124, printed p.9, PDF p.10). Suppose that `M/N → α ∈ (0,∞)`
and that a sequence of online algorithms satisfies `P(min_{1≤i≤M} X_{N,i} ≥ κ) → 1`. Then there
exist a filtered probability space with filtration `G`, a `G`-Brownian motion `B`, and a
`G`-progressively measurable process `a` such that `B_1 + ∫_0^1 a_t dt ≥ κ` a.s. and
`E a_t² ≤ 2/(πα)` for a.e. `t ∈ [0,1]` (12).

**Formalization Note** The probability space is existential, in `Type`; time is `ℝ≥0` (only
`[0,1]` matters). The path integral is a Bochner integral; since `a` is jointly measurable and
`E a_t²` is bounded on `[0,1]`, the paths are a.s. integrable there. -/
theorem proposition_3_1 (α κ : ℝ) (hα : 0 < α) (Mseq : ℕ → ℕ)
    (hM : Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α))
    (σ : ∀ N : ℕ, Fin N → (Fin (Mseq N) × Fin N → ℝ) → ℝ)
    (hσ : ∀ N, IsOnlineAlg (Mseq N) N (σ N))
    (hsucc : Tendsto (fun N : ℕ => gaussMat (Mseq N) N (successSet (σ N) κ)) atTop (𝓝 1)) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω), letI := mΩ;
      ∃ (P : Measure Ω) (_ : IsProbabilityMeasure P) (G : Filtration ℝ≥0 mΩ)
        (B a : ℝ≥0 → Ω → ℝ),
        IsBrownianWrt G B P ∧ IsStronglyProgressive G a ∧
        (∀ᵐ ω ∂P, κ ≤ ctrlTerminal B a 1 ω) ∧
        ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          secondMoment P a t ≤ ENNReal.ofReal (2 / (Real.pi * α)) := by sorry

end ABPOnline
