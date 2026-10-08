-- Prove2me | Theorems.Thm_BesbesZeevi_Nonparametric_step4_regret_bound
-- name    : BesbesZeevi.Nonparametric.step4_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:51:34.471497+00:00
-- url     : https://prove2.me/theorems/dcab77e3-c33b-4dde-92b9-69c3f1929736
-- title:
--   Proposition 1, Step 4: $\mathcal R^\pi_n(x,T;\lambda)\le C_{12}(u_n+\tau_n)$ uniformly over $\lambda\in\mathcal L$
-- statement:
--   Use the tuning of Proposition 1. There is a constant $C_{12}>0$, independent of the demand function and of $n$, such that the following holds. For every $n\ge1$ and every $\lambda\in\mathcal L$, the regret of Algorithm 1 $\pi(\tau_n,\kappa_n)$ satisfies
--
--   $$
--   \mathcal R^\pi_n(x,T;\lambda)\ \le\ C_{12}\,(u_n+\tau_n).
--   $$
--
--   Substituting the tuning into $u_n+\tau_n$ gives the rate of Proposition 1.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 31 (PDF 33), proof of Proposition 1, Step 4

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_BesbesZeevi_Nonparametric_Model
import Definitions.Def_BesbesZeevi_Nonparametric_Algorithm

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

namespace BesbesZeevi.Nonparametric

/-- Proof of Proposition 1, Step 4, p. 31: `R^π_n(x, T; λ) ≤ C₁₂ (u_n + τ_n)` for all `λ ∈ 𝓛`,
with `C₁₂` independent of `λ` and `n`. -/
theorem step4_regret_bound (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x) (hT : 0 < T)
    (c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ) :
    ∃ C₁₂ : ℝ, 0 < C₁₂ ∧
      ∀ (Ω : Type*) [MeasureSpace Ω] (N : ℝ → Ω → ℕ), IsPoissonProcess N 1 →
      ∀ n : ℕ, 1 ≤ n → ∀ lam : ℝ → ℝ, L.Mem P lam →
        regret P lam x T n (τ n) (κ n) N ≤ C₁₂ * (uSeq n (τ n) (κ n) + τ n) := by sorry

end BesbesZeevi.Nonparametric
