-- Prove2me | Theorems.Thm_FairDiffusionLimit_lemma_22
-- name    : FairDiffusionLimit.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:28.27771+00:00
-- url     : https://prove2.me/theorems/b322a1ec-658e-4126-8620-fb00d23d33e9
-- title:
--   Lemma 22 — a sequence of random vectors is tight iff it has a pointwise uniformly bounded coupling
-- statement:
--   Let $w_k$, $k=0,1,2,\dots$, be random vectors in $\mathbb R^d$ with laws $\mu_k$. Then $\{w_k\}$ is tight if and only if there are random vectors $\tilde w_k$ on one common probability space $\Omega$ with $\tilde w_k\overset{d}{=}w_k$ for every $k$ such that, for **every** $\omega\in\Omega$,
--   $$\sup_k|\tilde w_k(\omega)|<\infty .$$
--
--   This representation is used at the start of the proof of Proposition 2, to start the networks from tight initial laws.
--
--   **Formalization Note** Tightness is Mathlib's `IsTightMeasureSet` of the set of laws; $|\cdot|$ is the $\ell^1$ norm (any norm on $\mathbb R^d$ gives the same statement).
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Lemma 22, p.43 (PDF 43)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Lemma 22** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 43): a sequence of random vectors `w_k` (with laws `μ_k` on `ℝ^d`) is
tight if and only if there are random vectors `w̃_k` with `w̃_k =ᵈ w_k`, all on one probability space,
such that `sup_k |w̃_k(ω)| < ∞` for **every** `ω`. -/
theorem lemma_22 {d : ℕ} (μ : ℕ → ProbabilityMeasure (Fin d → ℝ)) :
    IsTightMeasureSet (Set.range fun k => (μ k : Measure (Fin d → ℝ))) ↔
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (w : ℕ → Ω → Fin d → ℝ),
        IsProbabilityMeasure P ∧ (∀ k, Measurable (w k)) ∧
        (∀ k, P.map (w k) = (μ k : Measure (Fin d → ℝ))) ∧
        ∀ ω, BddAbove (Set.range fun k => l1 (w k ω)) := by sorry

end FairDiffusionLimit
