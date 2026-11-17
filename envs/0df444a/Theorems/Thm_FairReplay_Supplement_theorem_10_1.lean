-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_1
-- name    : FairReplay.Supplement.theorem_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:51:09.602214+00:00
-- url     : https://prove2.me/theorems/903eecb5-b6c7-4dc5-91e6-161a9d84bc77
-- title:
--   Theorem 10.1 — static Gaussian tester with $8\log(2m/\delta)\Psi(H,\nu)/\gamma^2+|V_+(H)|$ calls
-- statement:
--   Let $H$ be a residual fairness graph with $m=|E(H)|\ge 1$ edges, let $\nu_v>0$ be the known standard deviations of the Gaussian delta oracle $Z_v\sim N(\theta_v,\nu_v^2)$, let $\gamma>0$ be the margin and $\delta\in(0,1)$. Consider patch-neutrality $H_0:\theta_u=\theta_v$ for every edge of $H$ against $H_1:|\theta_u-\theta_v|\ge\gamma$ for some edge.
--
--   Then there is a **non-adaptive** tester — call counts $N_v$ fixed in advance and a decision of the resulting independent samples — using
--   $$\sum_v N_v\ \le\ \frac{8\log(2m/\delta)}{\gamma^2}\,\Psi(H,\nu)+|V_+(H)|$$
--   Gaussian delta-oracle calls, which rejects with probability at most $\delta$ under every $\theta\in H_0$ and accepts with probability at most $\delta$ under every $\theta\in H_1$.
--
--   Together with Theorem 10.2 this shows that the graph allocation $\Psi(H,\nu)$ governs Gaussian fairness-regression testing up to confidence constants and a $\log|E|$ factor.
--
--   Differences from the source:
--   - encoding: a non-adaptive Gaussian delta-oracle tester → call counts N : Fin n → ℕ and a measurable decision φ of the sample vector, whose law is the product over v of N_v independent N(θ_v, ν_v²) draws; reason: non-adaptive = allocation fixed before sampling; the samples of distinct calls are independent
--   - encoding: known variances ν_v² > 0 → standard deviations ν_v > 0, variance ν_v² (Real.toNNReal); reason: same family of laws
--   - encoding: residual graph H, m = |E(H)| → SimpleGraph on Fin n with decidable adjacency, m = H.edgeFinset.card; reason: finite undirected graph without loops
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.1, eq. (15), p.11 (PDF p.13); §3, eq. (3), p.3

import Mathlib
import Definitions.Def_FairReplay_Supplement_activeVertices
import Definitions.Def_FairReplay_Supplement_gaussianModel
import Definitions.Def_FairReplay_Supplement_gaussAlloc

open MeasureTheory ProbabilityTheory

namespace FairReplay.Supplement

/-- **Theorem 10.1 (Static upper bound)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.1, eq. (15), p.11 (PDF p.13), with §3,
p.3): "Let m = |E(H)| ≥ 1. For δ ∈ (0, 1), a non-adaptive Gaussian delta-oracle tester exists using at
most 8 log(2m/δ)/γ² Ψ(H, ν) + |V+(H)| (15) Gaussian delta-oracle calls and having error probability
at most δ."

Let `H` be a residual graph on `Fin n` with `m ≥ 1` edges, `ν_v > 0` the known standard deviations,
`γ > 0` the margin and `δ ∈ (0, 1)`. There are call counts `N_v`, fixed in advance, and a measurable
decision `φ` of the independent samples (`N_v` draws of `N(θ_v, ν_v²)` at each `v`; `φ = true` means
"reject patch-neutrality") such that `Σ_v N_v ≤ 8 log(2m/δ) Ψ(H, ν)/γ² + |V+(H)|`, the test rejects
with probability at most `δ` for every `θ` with `θ_u = θ_v` on all edges, and accepts with probability
at most `δ` for every `θ` with `|θ_u − θ_v| ≥ γ` on some edge.

**Formalization Note** A non-adaptive tester is a fixed allocation of calls plus a decision of the
resulting samples; the sample law is the product of the per-vertex Gaussian laws of
`gaussianModel θ ν`. Logarithms are natural. -/
theorem theorem_10_1 {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (ν : Fin n → ℝ)
    (hν : ∀ v, 0 < ν v) (γ : ℝ) (hγ : 0 < γ) (hm : 1 ≤ H.edgeFinset.card) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ∃ (N : Fin n → ℕ) (φ : ((v : Fin n) → Fin (N v) → ℝ) → Bool),
      Measurable φ ∧
      ((∑ v, N v : ℕ) : ℝ) ≤
        8 * Real.log (2 * H.edgeFinset.card / δ) / γ ^ 2 * gaussAlloc H ν +
          (activeVertices H).card ∧
      (∀ θ : Fin n → ℝ, (∀ u v, H.Adj u v → θ u = θ v) →
        (Measure.pi fun v => Measure.pi fun _ : Fin (N v) => (gaussianModel θ ν).P v)
          {z | φ z = true} ≤ ENNReal.ofReal δ) ∧
      (∀ θ : Fin n → ℝ, (∃ u v, H.Adj u v ∧ γ ≤ |θ u - θ v|) →
        (Measure.pi fun v => Measure.pi fun _ : Fin (N v) => (gaussianModel θ ν).P v)
          {z | φ z = false} ≤ ENNReal.ofReal δ) := by sorry

end FairReplay.Supplement
