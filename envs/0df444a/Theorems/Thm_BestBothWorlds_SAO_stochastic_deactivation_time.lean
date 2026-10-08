-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_stochastic_deactivation_time
-- name    : BestBothWorlds.SAO.stochastic_deactivation_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:46:48.802419+00:00
-- url     : https://prove2.me/theorems/bb37e697-0820-4c2e-90c9-6ff4546a671c
-- title:
--   §4.2 — on the good event, a suboptimal arm is deactivated by time $260K\log(\beta)/\Delta_i^2$
-- statement:
--   Under the same assumptions as the previous statement — $K\ge2$, $n\ge K$, $\delta\in(0,1)$, $\beta=10Kn^3\delta^{-1}$, distributions $\nu_i$ on $[0,1]$ with means $\mu_i$, a reward table with entries in $[0,1]$, an arm path along which (21) and (23) hold for every arm $i$ and every $t\in\{1,\dots,\tau_0\}$ — every arm $i$ with gap $\Delta_i>0$ satisfies
--   $$\tau_i\le260\,\frac{K\log\beta}{\Delta_i^2},$$
--   where $\tau_i$ denotes $\min(\tau_i,\tau_0)$.
--
--   Together with (24) and (27), this bounds the pseudo-regret $\overline R_n=\sum_i\Delta_iT_i(n)$ on the good event.
--
--   **Formalization Note** The paper proves this from (26) for deactivated arms. The statement covers every arm with $\Delta_i>0$, as the paper's sentence does; for an arm that is never deactivated ($\tau_i=n$), the bound follows from (12) failing at time $n$.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 18, §4.2 ("for any arm i with ∆i > 0, one can see that (26) implies: τi ≤ 259 K log(β)/∆i² + 1 ≤ 260 K log(β)/∆i²")

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- §4.2 (p. 18): on a run of SAO with `β = 10Kn³δ⁻¹` on a reward table of the stochastic model
along which (21) and (23) hold for every arm `i` and every time `t ∈ {1, …, τ₀}`, every arm `i`
with `Δ_i > 0` satisfies `τ_i ≤ 260 K log(β)/Δ_i²`. -/
theorem stochastic_deactivation_time (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (ω : Fin n → Fin K → ℝ)
    (hω : ∀ r i, ω r i ∈ Set.Icc (0 : ℝ) 1) (I : Fin n → Fin K)
    (h21 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I),
      |estAvg (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) (tableAdv ω) I i t - mean ν i| ≤
        estRadius K (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i) (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i) t
          (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)))
    (h23 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I),
      1 ≤ pullCount I i t →
        |algAvg (tableAdv ω) I i t - mean ν i| ≤
          Real.sqrt (2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) / pullCount I i t)) :
    ∀ i : Fin K, 0 < gap (mean ν) i →
      (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i : ℝ) ≤ 260 * K * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) / gap (mean ν) i ^ 2 := by sorry

end BestBothWorlds.SAO
