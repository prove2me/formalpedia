-- Prove2me | Theorems.Thm_ABPOnline_proposition_4_8
-- name    : ABPOnline.proposition_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:48.136847+00:00
-- url     : https://prove2.me/theorems/558657e4-49fd-4339-aab2-d64f167dd453
-- title:
--   Proposition 4.8 — achievability below the threshold: Algorithm 1 reaches margin $\kappa+\rho$
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$ and $0<\alpha<2/(\pi E_\star(\kappa))$. Then there exists $\rho>0$ such that, for every even $p>4$, every $c_F\in(0,c_\alpha)$ and every final-block triple $(h_0,s_p,v)$ with the property of Lemma 4.5, Algorithm 1 with a suitable fixed choice of its control parameters (a rational $T\in(0,1)$, a target $a$ and a control $\beta$ of the form in Definition 4.2) satisfies
--   $$
--   \mathbb P\Big(\min_{i\le M}X_{N,i}\ge\kappa+\rho\Big)\longrightarrow1
--   $$
--   for every integer sequence $M_N$ with $M_N/N\to\alpha$.
--
--   Together with Corollary 3.3 this proves the threshold identity of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: E⋆(κ) defined from a standard Brownian motion B = (B_t)_{0≤t≤1} with its completed natural filtration → the statement holds for every process B with IsBrownianOn1 B P on every probability space, with E⋆ computed on that B; reason: E⋆(κ) depends only on the law of B; the source's Brownian motion is one such process
--   - encoding: α_on(κ) and E⋆(κ) as a supremum and an infimum of reals, with 2/(πE⋆(κ)) → values in ℝ≥0∞ and the identity in ℝ≥0∞; reason: no junk value for an empty or unbounded set; by Lemma 2.3, 0 < E⋆(κ) < ∞, so the identity is the real one
--   - encoding: α a constraint density, α ∈ (0, ∞) (§2.1) → hypothesis 0 < α; reason: the standing assumption of §2.1 made explicit
--   - encoding: M/N → α (every integer sequence M_N) → ∀ Mseq : ℕ → ℕ with (Mseq N : ℝ)/N → α; reason: the same; (Mseq N)/N is 0 at N = 0, which does not affect the limit
--   - generalization: Algorithm 1 with one fixed even p > 4, one c_F ∈ (0, c_α) and the feedback of Lemma 4.5 → ρ first; then for every even p > 4, every c_F ∈ (0, c_α) and every triple (h₀, s_p, v) with IsFinalBlockFeedback p c_F h₀ s_p v there are T, a, β; reason: the paper's choices are instances; the proof (p.18) works for each of them with ρ = 2ρ₀ from Lemma 4.1
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Proposition 4.8, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianOn1
import Definitions.Def_ABPOnline_IsOnlineAlg
import Definitions.Def_ABPOnline_Estar
import Definitions.Def_ABPOnline_IsFinalBlockFeedback
import Definitions.Def_ABPOnline_alg1

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ABPOnline

/-- **Proposition 4.8** (arXiv:2609.02124, printed p.18, PDF p.19). If `α < 2/(πE⋆(κ))`, then there
exists `ρ > 0` such that Algorithm 1, for a suitable fixed choice of its control parameters,
satisfies `P(min_{i≤M} X_{N,i} ≥ κ + ρ) → 1` whenever `M/N → α`.

**Formalization Note** `ρ` is chosen first; then for every even `p > 4`, every `c_F ∈ (0, c_α)` and
every final-block triple `(h₀, s_p, v)` with the property of Lemma 4.5 there are parameters
`T ∈ (0,1)` rational, `a` and `β` of the form in Definition 4.2 that work for every sequence
`M_N/N → α`. The paper fixes one `p`, one `c_F` and its own feedback; those are instances.
`E⋆` is computed on a standard Brownian motion `B`, in `ℝ≥0∞`; `α > 0` is the standing assumption
of §2.1. -/
theorem proposition_4_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianOn1 B P) (κ α : ℝ) (hα : 0 < α)
    (hlt : ENNReal.ofReal α < 2 / (ENNReal.ofReal Real.pi * Estar P B κ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (p : ℕ) (cF h₀ : ℝ) (sp : ℝ → ℝ) (v : ℕ → ℕ → ℝ → ℝ → ℝ),
      Even p → 4 < p → 0 < cF → cF < cAlpha α → IsFinalBlockFeedback p cF h₀ sp v →
      ∃ (T : ℚ) (a : ℝ) (β : SimpleCtrl), 0 < T ∧ T < 1 ∧ β.IsValidOn T ∧
        ∀ Mseq : ℕ → ℕ, Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α) →
          Tendsto (fun N : ℕ =>
            gaussMat (Mseq N) N (successSet (alg1 T a β v (Mseq N) N) (κ + ρ))) atTop (𝓝 1) := by sorry

end ABPOnline
