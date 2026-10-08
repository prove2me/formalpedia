-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_stochastic_no_switch
-- name    : BestBothWorlds.SAO.stochastic_no_switch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:46:37.020064+00:00
-- url     : https://prove2.me/theorems/6f9ffc20-f93a-4579-8a22-4259a44f0c97
-- title:
--   §4.2 — on the good event, Exp3.P is never started in the stochastic model ($\tau_0=n$)
-- statement:
--   Let $K\ge2$, $n\ge K$, $\delta\in(0,1)$ and $\beta=10Kn^3\delta^{-1}$. Let $\nu_1,\dots,\nu_K$ be distributions on $[0,1]$ with means $\mu_i$. Fix a reward table with entries in $[0,1]$ and an arm path, and consider the run of SAO with parameter $\beta$ along them. Suppose that for every arm $i$ and every $t\in\{1,\dots,\tau_0\}$:
--
--   1. (21) holds: $\big|\widetilde H_{i,t}-\mu_i\big|\le\sqrt{4\big(\frac{K\min(\tau_i,t)}{t^2}+\frac{\max(t-\tau_i,0)}{q_i\tau_i t}\big)\log\beta+5\big(\frac{K\log\beta}{\min(\tau_i,t)}\big)^2}$;
--   2. (23) holds: if $T_i(t)\ge1$ then $\big|\widehat H_{i,t}-\mu_i\big|\le\sqrt{2\log\beta/T_i(t)}$.
--
--   Then none of the tests (13)–(15) is ever satisfied, so Exp3.P is never started:
--   $$\tau_0=n.$$
--
--   This is a deterministic statement about the run's own quantities ($\tau_0$, $\tau_i$, $q_i$, the estimates), which SAO computes. Together with Lemma 4.6 and the stochastic part of Lemma 4.5, it shows that in the stochastic model SAO never switches to Exp3.P, with high probability.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, pp. 17–18, §4.2 ("In conclusion we proved that Exp3 is never started in the stochastic model, that is τ0 = n.")

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- §4.2 (pp. 17–18): on a run of SAO with `β = 10Kn³δ⁻¹` on a reward table of the stochastic
model along which (21) and (23) hold for every arm `i` and every time `t ∈ {1, …, τ₀}`, none of
the tests (13)–(15) is ever satisfied: Exp3.P is never started, `τ₀ = n`. -/
theorem stochastic_no_switch (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
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
    tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I = n := by sorry

end BestBothWorlds.SAO
