-- Prove2me | Theorems.Thm_BewleyGE_lemma_3
-- name    : BewleyGE.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:28:20.437982+00:00
-- url     : https://prove2.me/theorems/46ba3ec0-52ea-4c41-8bdc-ed09197f85d8
-- title:
--   Lemma 3 — bounded convergence with varying measures
-- statement:
--   Let $w_k:\mathbb R\to\mathbb R$ be measurable and uniformly bounded, $|w_k(a)|\le C$, and suppose $w_k$ **converges continuously** to $w$: $w_k(a_k)\to w(a)$ whenever $a_k\to a$. If probability measures $\lambda_k$ on $\mathbb R$ converge weakly to a probability measure $\lambda$, then
--   $$
--   \lim_{k\to\infty}\int w_k(a)\,\lambda_k(da)=\int w(a)\,\lambda(da).
--   $$
--
--   This is the tool that turns continuity of the policy in prices into continuity of aggregate demand (Serfozo 1982, Theorem 3.3).
--
--   Differences from the source:
--   - reading: wₙ : ℝ → ℝ uniformly bounded (integrals ∫ wₙ dλₙ) → each wₙ measurable and uniformly bounded; reason: the integrals presuppose measurability (Serfozo 1982, Thm 3.3); without it the Bochner integral is 0 and the statement is false
--   - encoding: λₙ ∈ P(ℝ) converges weakly to λ → probability measures with ∫ f dλₙ → ∫ f dλ for bounded continuous f; reason: the definition of weak convergence
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Lemma 3 and the definition of continuous convergence, p.22

import Mathlib
import Definitions.Def_BewleyGE_WeakConv

open MeasureTheory Filter Topology

namespace BewleyGE

/-- **Lemma 3 (bounded convergence with varying measures).** Light, arXiv:1906.06810v2,
Lemma 3, p.22: "Assume that wₙ : R → R is a uniformly bounded sequence of functions. If
wₙ : R → R converges continuously to w and λₙ ∈ P(R) converges weakly to λ ∈ P(R) then
lim_{n→∞} ∫ wₙ(a) λₙ(da) = ∫ w(a) λ(da)." Continuous convergence (p.22): `wₙ(aₙ) → w(a)`
whenever `aₙ → a`.

**Formalization Note.** Each `wₙ` is assumed measurable: the paper leaves it implicit (its source,
Serfozo 1982, Theorem 3.3, works with measurable functions), and without it the Bochner
integrals are junk. The limit `w` needs no hypothesis (continuous convergence makes it
continuous). -/
theorem lemma_3 (w : ℕ → ℝ → ℝ) (w₀ : ℝ → ℝ) (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    (hν : ∀ k, IsProbabilityMeasure (ν k)) (hν₀ : IsProbabilityMeasure ν₀)
    (hmeas : ∀ k, Measurable (w k)) (hbdd : ∃ C : ℝ, ∀ k a, |w k a| ≤ C)
    (hcc : ∀ (a : ℝ) (s : ℕ → ℝ), Tendsto s atTop (𝓝 a) →
      Tendsto (fun k => w k (s k)) atTop (𝓝 (w₀ a)))
    (hweak : WeakConv ν ν₀) :
    Tendsto (fun k => ∫ a, w k a ∂(ν k)) atTop (𝓝 (∫ a, w₀ a ∂ν₀)) := by sorry

end BewleyGE
