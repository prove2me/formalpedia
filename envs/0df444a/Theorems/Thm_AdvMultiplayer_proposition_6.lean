-- Prove2me | Theorems.Thm_AdvMultiplayer_proposition_6
-- name    : AdvMultiplayer.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:44.996187+00:00
-- url     : https://prove2.me/theorems/7d4b7063-7726-4d09-ba2b-df8360e81495
-- title:
--   Proposition 6 — auxiliary learning bound
-- statement:
--   For every fixed $m$-set $S$,
--   $$R_{\mathrm{aux}}(S)\le\frac{2\log\binom Km+m/16}\eta+\Big(16m^2+\frac{16}{11}R+32m+1024(K-m+1)L_{\mathrm{stab}}\Big)\eta T+\frac{mT}{\eta D}+mTN^{-2}.$$
--   This is the learning part of the regret bound, before transport costs.
--
--   Differences from the source:
--   - encoding: rewards rounded down to multiples of 1/D (Section 3 onward, p.6) → `IsRounded`; reason: standing convention of the section; the same matrices
--   - reading: S chosen independently of the players’ randomness → every deterministic m-set S; reason: an independent random S follows by integrating, and the maximizer of the original matrix is deterministic
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Proposition 6, p.19, (17)

import Mathlib
import Definitions.Def_AdvMultiplayer_Learner

open MeasureTheory

namespace AdvMultiplayer

/-- **Proposition 6 (auxiliary learning bound).** Gan, arXiv:2610.05688, Proposition 6, p.19, (17).

**Formalization Note.** Stated for every deterministic `m`-set `S`. An `S` chosen independently of the
players' randomness follows by integrating, and `S` may maximize the original matrix. `R_aux` runs over
all enabled rounds, including those after overflow (p.18). -/
theorem proposition_6 (p : Size) (η : ℝ) (hη : RateOK p η) (r : Rewards p) (hr : IsRounded p r)
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (L : Learner p Ω) (Hpre Hupd Hprop : ℕ → MeasurableSpace Ω)
    (hL : L.IsRealization η μ ℱ r Hpre Hupd Hprop) (S : Finset (Fin p.K)) (hS : S ∈ mSets p) :
    L.Raux η μ r S ≤
      (2 * Real.log (p.K.choose p.m : ℝ) + (p.m : ℝ) / 16) / η
        + (16 * (p.m : ℝ) ^ 2 + 16 / 11 * (p.Rconst : ℝ) + 32 * p.m
            + 1024 * ((p.K - p.m + 1 : ℕ) : ℝ) * p.Lstab) * η * p.T
        + (p.m : ℝ) * p.T / (η * p.D) + (p.m : ℝ) * p.T / (p.N : ℝ) ^ 2 := by sorry

end AdvMultiplayer
