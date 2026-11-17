-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_2
-- name    : FairReplay.Supplement.theorem_10_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:51:41.631204+00:00
-- url     : https://prove2.me/theorems/0ace9d1d-858d-4f90-aa26-e34734739ab9
-- title:
--   Theorem 10.2 — adaptive Gaussian lower bound $\mathbb E_0[T]\ge 2\,\mathrm{kl}(1-\delta,\delta)\Psi(H,\nu)/\gamma^2$
-- statement:
--   In the Gaussian delta-oracle model with known standard deviations $\nu_v>0$, margin $\gamma>0$ and $\delta\in(0,1/2)$, let $(\pi,T,\psi)$ be an adaptive tester whose type-I error at the null instance $\theta\equiv 0$ is at most $\delta$, whose type-II error is at most $\delta$ at every $\theta$ with $|\theta_u-\theta_v|\ge\gamma$ on some edge of $H$, and whose expected number of calls at $\theta\equiv0$ is finite. Then
--   $$\mathbb E_0[T]\ \ge\ \frac{2\,\mathrm{kl}(1-\delta,\delta)}{\gamma^2}\,\Psi(H,\nu),$$
--   with $\mathrm{kl}(x,y)=x\log\frac xy+(1-x)\log\frac{1-x}{1-y}$.
--
--   This is the adaptive null-side converse to Theorem 10.1: no adaptive allocation of oracle calls beats the graph allocation by more than confidence constants.
--
--   Differences from the source:
--   - generalization: δ-correct: type I ≤ δ under every null θ (θ_u = θ_v on all edges) → type I ≤ δ assumed only at θ ≡ 0; reason: the paper's δ-correctness implies the Lean hypothesis, so the Lean theorem specializes to the paper's
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
--   - encoding: Gaussian delta-oracle calls at the vertices of H → the tester may call any vertex of Fin n; reason: calls outside V+(H) carry no information about H's edges; allowing them only enlarges the tester class
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.2, eq. (18), p.12 (PDF p.14)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_expectedRounds
import Definitions.Def_FairReplay_Supplement_gaussianModel
import Definitions.Def_FairReplay_Supplement_gaussAlloc

open MeasureTheory

namespace FairReplay.Supplement

/-- **Theorem 10.2 (Adaptive lower bound)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.2, eq. (18), p.12 (PDF p.14), with §3,
p.3): "For δ ∈ (0, 1/2), every adaptive δ-correct tester with finite expected stopping time (measured
in Gaussian delta-oracle calls) has, on the null instance θ ≡ 0, E0[T] ≥ 2kl(1 − δ, δ)/γ² Ψ(H, ν). (18)"

Let `H` be a residual graph on `Fin n`, `ν_v > 0`, `γ > 0` and `δ ∈ (0, 1/2)`. Every adaptive tester
`(π, T, ψ)` on the Gaussian delta-oracle model that rejects with probability at most `δ` at `θ ≡ 0`,
fails to reject with probability at most `δ` at every `θ` with `|θ_u − θ_v| ≥ γ` on some edge of `H`,
and has `E₀[T] < ∞`, satisfies `E₀[T] ≥ 2 kl(1 − δ, δ) Ψ(H, ν)/γ²`.

**Formalization Note** Testers are adaptive, possibly randomized policies over all vertices of `Fin n`
(one call = one round), with a stopping time `T` of the transcript filtration and a decision measurable
for the stopped σ-algebra; a run that never stops counts as an error under an alternative. Only
type I at `θ ≡ 0` is assumed, which the paper's δ-correctness implies. `kl` is
`BanditAlgorithm.bernoulliRelativeEntropy`. -/
theorem theorem_10_2 {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (ν : Fin n → ℝ)
    (hν : ∀ v, 0 < ν v) (γ : ℝ) (hγ : 0 < γ) (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ < 1 / 2)
    (π : BanditAlgorithm.BanditPolicy n) (T : (ℕ → Fin n × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin n × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T)
    (hψ : Measurable[hT.measurableSpace] ψ)
    (hI : BanditAlgorithm.banditTrajMeasure (gaussianModel 0 ν) π {ω | T ω < ⊤ ∧ ψ ω = true} ≤
      ENNReal.ofReal δ)
    (hII : ∀ θ : Fin n → ℝ, (∃ u v, H.Adj u v ∧ γ ≤ |θ u - θ v|) →
      BanditAlgorithm.banditTrajMeasure (gaussianModel θ ν) π {ω | ¬ (T ω < ⊤ ∧ ψ ω = true)} ≤
        ENNReal.ofReal δ)
    (hfin : expectedRounds (gaussianModel 0 ν) π T < ⊤) :
    ENNReal.ofReal (2 * BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ / γ ^ 2 *
        gaussAlloc H ν) ≤
      expectedRounds (gaussianModel 0 ν) π T := by sorry

end FairReplay.Supplement
