-- Prove2me | Theorems.Thm_AdvMultiplayer_lemma_4
-- name    : AdvMultiplayer.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:48.109493+00:00
-- url     : https://prove2.me/theorems/207efa80-78b5-41c3-9f76-120b4deb4e92
-- title:
--   Lemma 4 — queue bound
-- statement:
--   For a realization of Algorithm 1 with interface (I1)-(I4), rounded rewards and an admissible rate: $\Pr(\tau_*\le T)\le N^{-2}$; in the stopped continuation every normalized backlog $b_t(i)$ is at most $2B_{\mathrm{cap}}$; and
--   $$\mathbb E\sum_{t\le\tau_*,\ t\text{ enabled}}\sum_i\theta_{w_t}(i)b_t(i)\le\frac2{11}\Big(R+\frac{33}2m\Big)T,$$
--   with $R=64m^2(2K-m)$. The bound on the weighted backlog controls the cost of late service in Proposition 6.
--
--   Differences from the source:
--   - encoding: rewards rounded down to multiples of 1/D (Section 3 onward, p.6) → `IsRounded`; reason: standing convention of the section; the same matrices
--   - encoding: backlogs bounded with no range on t → rounds 1 ≤ t ≤ T+1; reason: those are the rounds of the process
--   - encoding: expectation in (15) → `Integrable` is stated as a conclusion; reason: so that the integral is not a junk value
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Lemma 4, p.17, (15)

import Mathlib
import Definitions.Def_AdvMultiplayer_Learner

open MeasureTheory

namespace AdvMultiplayer

/-- **Lemma 4 (queue bound).** Gan, arXiv:2610.05688, Lemma 4, p.17, (15): `Pr(τ_* ≤ T) ≤ N⁻²`; in the
stopped continuation every normalized backlog is at most `2B_cap`; and the weighted backlog bound (15).

**Formalization Note.** The statement is about any realization of Algorithm 1 with interface
(I1)–(I4), with rounded rewards and any admissible dyadic rate (standing assumptions of Section 3,
p.13). Backlogs are bounded for all rounds `1 ≤ t ≤ T+1`. -/
theorem lemma_4 (p : Size) (η : ℝ) (hη : RateOK p η) (r : Rewards p) (hr : IsRounded p r)
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (L : Learner p Ω) (Hpre Hupd Hprop : ℕ → MeasurableSpace Ω)
    (hL : L.IsRealization η μ ℱ r Hpre Hupd Hprop) :
    μ {ω | L.tauStar η ω ≤ (p.T : ℕ∞)} ≤ ENNReal.ofReal (1 / (p.N : ℝ) ^ 2) ∧
    (∀ ω, ∀ t ∈ Finset.Icc 1 (p.T + 1), ∀ i, L.b η t ω i ≤ 2 * Size.BcapOf η) ∧
    Integrable (fun ω => ∑ t ∈ Finset.Icc 1 p.T, by
      classical exact if L.retained η t ω ∧ L.enabled η t ω then
        ∑ i, theta p (L.w t ω) i * L.b η t ω i else 0) μ ∧
    ∫ ω, (∑ t ∈ Finset.Icc 1 p.T, by
      classical exact if L.retained η t ω ∧ L.enabled η t ω then
        ∑ i, theta p (L.w t ω) i * L.b η t ω i else 0) ∂μ
      ≤ 2 / 11 * ((p.Rconst : ℝ) + 33 / 2 * p.m) * p.T := by sorry

end AdvMultiplayer
