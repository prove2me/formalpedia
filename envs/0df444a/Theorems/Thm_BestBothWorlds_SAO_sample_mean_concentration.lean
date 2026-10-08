-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_sample_mean_concentration
-- name    : BestBothWorlds.SAO.sample_mean_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:46:00.166653+00:00
-- url     : https://prove2.me/theorems/b0242b1c-5bd2-45c6-a09b-504fb4a83ab0
-- title:
--   Lemma 4.6 — concentration of the sample mean $\widehat H_{i,t}$, uniformly in $t$
-- statement:
--   Consider SAO with parameter $\beta>1$ on $K\ge2$ arms and $n\ge K$ rounds in the stochastic model with reward distributions $\nu_1,\dots,\nu_K$ on $[0,1]$ and means $\mu_1,\dots,\mu_K$. Fix an arm $i$ and $\delta>0$. With probability at least $1-\delta$, for every time $t\in\{1,\dots,n\}$ with $T_i(t)\ge1$,
--   $$\big|\widehat H_{i,t}-\mu_i\big|\le\sqrt{\frac{2\log(2n\delta^{-1})}{T_i(t)}}.$$
--   Here $\widehat H_{i,t}$ is the average of the rewards of arm $i$ observed up to time $t$, and $T_i(t)$ is the number of times arm $i$ was played up to time $t$.
--
--   The bound is uniform over $t$, unlike Lemmas 4.5 and 4.7. It gives (23).
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 16, Lemma 4.6

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- Lemma 4.6 (p. 16): for a fixed arm `i`, in the stochastic model, with probability at least
`1 - δ`, for every time `t ∈ {1, …, n}` with `T_i(t) ≥ 1`,
`|Ĥ_{i,t} - µ_i| ≤ √(2 log(2nδ⁻¹)/T_i(t))`. -/
theorem sample_mean_concentration (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (β : ℝ) (hβ : 1 < β)
    (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (i : Fin K) (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ probStoch n (sao K n β) ν (fun ω I =>
      ∀ t ∈ Finset.Icc 1 n, 1 ≤ pullCount I i t →
        |algAvg (tableAdv ω) I i t - mean ν i| ≤
          Real.sqrt (2 * Real.log (2 * n / δ) / pullCount I i t)) := by sorry

end BestBothWorlds.SAO
