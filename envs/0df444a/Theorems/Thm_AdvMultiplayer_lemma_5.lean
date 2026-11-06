-- Prove2me | Theorems.Thm_AdvMultiplayer_lemma_5
-- name    : AdvMultiplayer.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:52.91137+00:00
-- url     : https://prove2.me/theorems/61d7957e-e7da-472f-8931-4edb18197898
-- title:
--   Lemma 5 — conditional slow-set law
-- statement:
--   Fix an episode starting at $\tau$ before any overflow, with exposed history $H_\tau$, and let $\mathcal E_t=\sigma(H_\tau,\tilde r_\tau,\dots,\tilde r_{t-1})$. For each round $t$ of the episode,
--   $$\Pr(U_t=U\mid\mathcal E_t)=p_t(U)\quad\text{on }\{t\le\tau_*\},$$
--   and $\{t\le\tau_*\}$ is $\mathcal E_t$-measurable. Thus revealing past estimates does not change the marginal law of the slow set, although it hides the proposals.
--
--   Differences from the source:
--   - encoding: rewards rounded down to multiples of 1/D (Section 3 onward, p.6) → `IsRounded`; reason: standing convention of the section; the same matrices
--   - encoding: random episode start τ → each event {τ = s} with s deterministic; reason: the event lies in H_s, so the statements are the same
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Lemma 5, p.18

import Mathlib
import Definitions.Def_AdvMultiplayer_Learner

open MeasureTheory

namespace AdvMultiplayer

/-- **Lemma 5 (conditional slow-set law).** Gan, arXiv:2610.05688, Lemma 5, p.18: for each round `t` of
an episode starting before overflow, `Pr(U_t = U | ℰ_t) = p_t(U)` on `{t ≤ τ_*}`, where
`ℰ_t = σ(H_τ, r̃_τ, …, r̃_{t-1})`, and `{t ≤ τ_*}` is `ℰ_t`-measurable.

**Formalization Note.** The episode start `τ` is a random time; the statement is given on each event
`{τ = s}`, which lies in `H_s`, with `s` deterministic. This is the same statement. -/
theorem lemma_5 (p : Size) (η : ℝ) (hη : RateOK p η) (r : Rewards p) (hr : IsRounded p r)
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (L : Learner p Ω) (Hpre Hupd Hprop : ℕ → MeasurableSpace Ω)
    (hL : L.IsRealization η μ ℱ r Hpre Hupd Hprop) (s t : ℕ) (hs : 1 ≤ s) (hst : s ≤ t)
    (ht : t < Learner.epEnd (p := p) η s) :
    MeasurableSet[L.Ehist η Hpre r s t] {ω | L.isStart s ω ∧ L.retained η t ω} ∧
    ∀ U ∈ Finset.powersetCard (p.m - 1) (Finset.univ : Finset (Fin p.K)), ∀ᵐ ω ∂μ,
      L.isStart s ω → L.retained η t ω →
        (μ[Learner.ind {ω | L.slow t ω = U} | L.Ehist η Hpre r s t]) ω =
          pw p (L.anchor t ω) (L.w t ω) U := by sorry

end AdvMultiplayer
