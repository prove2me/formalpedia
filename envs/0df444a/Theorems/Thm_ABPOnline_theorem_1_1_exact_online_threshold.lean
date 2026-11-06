-- Prove2me | Theorems.Thm_ABPOnline_theorem_1_1_exact_online_threshold
-- name    : ABPOnline.theorem_1_1_exact_online_threshold
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:42.8332+00:00
-- url     : https://prove2.me/theorems/4c27fa8d-d5e5-4be4-810b-d3ece0afa66f
-- title:
--   Theorem 1.1 — exact online threshold $\alpha_{\mathrm{on}}(\kappa)=2/(\pi E_\star(\kappa))$, achieved by an $O(MN)$ online algorithm
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$ and $E_\star(\kappa)$ the Brownian control value. For every fixed $\kappa\in\mathbb R$,
--   $$
--   \alpha_{\mathrm{on}}(\kappa)=\frac{2}{\pi E_\star(\kappa)} .
--   $$
--   Moreover, if $0<\alpha<2/(\pi E_\star(\kappa))$, then there are a constant $\rho>0$ and a deterministic online algorithm such that, for every integer sequence $M_N$ with $M_N/N\to\alpha$,
--   $$
--   \mathbb P\Big(\min_{1\le i\le M_N}\frac{(G\sigma)_i}{\sqrt N}\ge\kappa+\rho\Big)\longrightarrow1,
--   $$
--   and the algorithm uses $O(MN)$ arithmetic operations: it is a fixed real-RAM program that, on every $M\times N$ input with $M,N\ge1$, halts after emitting $N$ signs at cost at most $C\,MN$, and whose emitted signs form a deterministic online algorithm for every $M,N$. One program serves every sequence $M_N$.
--
--   The first part says the one-dimensional Brownian control problem gives the exact threshold for online feasibility of the asymmetric binary perceptron; the second gives an efficient algorithm at every density below it.
--
--   Differences from the source:
--   - generalization: E⋆(κ) defined from a standard Brownian motion B = (B_t)_{0≤t≤1} with its completed natural filtration → the statement holds for every process B with IsBrownianOn1 B P on every probability space, with E⋆ computed on that B; reason: E⋆(κ) depends only on the law of B; the source's Brownian motion is one such process
--   - encoding: α_on(κ) and E⋆(κ) as a supremum and an infimum of reals, with 2/(πE⋆(κ)) → values in ℝ≥0∞ and the identity in ℝ≥0∞; reason: no junk value for an empty or unbounded set; by Lemma 2.3, 0 < E⋆(κ) < ∞, so the identity is the real one
--   - encoding: σ_k ∈ {−1,+1} F^G_k-measurable, columns g_1, …, g_N → σ k a ±1-valued Borel function of the matrix, equal on matrices that agree in columns 0, …, k; columns indexed from 0; reason: equivalent on the canonical space of the Gaussian matrix
--   - encoding: M/N → α (every integer sequence M_N) → ∀ Mseq : ℕ → ℕ with (Mseq N : ℝ)/N → α; reason: the same; (Mseq N)/N is 0 at N = 0, which does not affect the limit
--   - encoding: α a constraint density, α ∈ (0, ∞) (§2.1) → hypothesis 0 < α; reason: the standing assumption of §2.1 made explicit
--   - reading: "This algorithm uses O(MN) arithmetic operations" → a fixed program of the real-RAM RAMInstr (finitely many real constants; +, −, ×, ÷, √, exp, log, Φ, comparisons, natural addition and subtraction, indirect addressing, a column read costing M, sign emission) that halts without fault on every M × N input with M, N ≥ 1 after emitting N signs, at cost ≤ C·M·N for one constant C, and whose signs are an online algorithm for all M, N; reason: the paper fixes no machine model; these are the operations Algorithm 1 uses (√ and log in Ψ, exp and Φ in the feedback (97)), each charged once
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Theorem 1.1, p.1 (PDF p.2)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianOn1
import Definitions.Def_ABPOnline_alphaOn
import Definitions.Def_ABPOnline_Estar
import Definitions.Def_ABPOnline_RAMInstr

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ABPOnline

/-- **Theorem 1.1 (Exact online threshold)** (Jo–Lee, arXiv:2609.02124, printed p.1, PDF p.2).
For every fixed `κ ∈ ℝ`, `α_on(κ) = 2/(πE⋆(κ))`. Moreover, if `α < 2/(πE⋆(κ))`, there are a
constant `ρ > 0` and a deterministic online algorithm such that, for every integer sequence
`M_N/N → α`, `P(min_{1≤i≤M_N} (Gσ)_i/√N ≥ κ + ρ) → 1`; the algorithm uses `O(MN)` arithmetic
operations.

**Formalization Note** `E⋆(κ)` is computed on an arbitrary standard Brownian motion `B` on an
arbitrary probability space; `α_on` and `E⋆` are in `ℝ≥0∞`. The algorithm is a program of the
real-RAM `RAMInstr` (a finite instruction list with finitely many real constants, fixed before
`M` and `N`); it reads `M` and `N` from its registers. For all `M, N ≥ 1` and every input matrix
it halts without fault after emitting `N` signs, at cost at most `C·M·N`; its signs form an online
algorithm in the sense of Definition 2.1 for all `M, N`; and one program serves every sequence
`M_N`. The density `α > 0` is the standing assumption of §2.1. -/
theorem theorem_1_1_exact_online_threshold {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianOn1 B P) (κ : ℝ) :
    alphaOn κ = 2 / (ENNReal.ofReal Real.pi * Estar P B κ) ∧
    ∀ α : ℝ, 0 < α → ENNReal.ofReal α < 2 / (ENNReal.ofReal Real.pi * Estar P B κ) →
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ prog : List RAMInstr, ∃ C : ℝ,
        (∀ M N : ℕ, 1 ≤ M → 1 ≤ N → ∀ G : Fin M × Fin N → ℝ,
          ∃ t : ℕ, RAMHaltsOK prog M N G t ∧
            ((ramExec prog M N G t).cost : ℝ) ≤ C * M * N) ∧
        (∀ M N : ℕ, IsOnlineAlg M N (fun k G => ramSign prog M N G k)) ∧
        ∀ Mseq : ℕ → ℕ, Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α) →
          Tendsto (fun N : ℕ => gaussMat (Mseq N) N
            (successSet (fun k G => ramSign prog (Mseq N) N G k) (κ + ρ))) atTop (𝓝 1) := by sorry

end ABPOnline
