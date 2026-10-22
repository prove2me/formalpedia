-- Prove2me | Theorems.Thm_DynamicAssortment_Separation_regret_le_sum_prob_nonoptimal
-- name    : DynamicAssortment.Separation.regret_le_sum_prob_nonoptimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T10:24:47.495545+00:00
-- url     : https://prove2.me/theorems/a38dc989-d505-49a8-8a65-ff12e4973a2c
-- title:
--   Final display (p. 403), first inequality — the regret is at most Σ_t ℙ{NO(t)}
-- statement:
--   Let $1\le C\le N$, $w_i>0$, $f$ a positive noise density, and $S^*$ an optimal-assortment selection. For every horizon $T$ and every admissible policy $\pi$ (nonanticipating, offering assortments of size at most $C$),
--   $$\mathcal R^\pi(T,\mu)\le\sum_{t=1}^{T}\mathbb P_\pi\{NO(t)\},\qquad NO(t)=\{S_t\neq S^*(\mu)\}.$$
--
--   The regret counts, in units of the optimal single-sale profit, the revenue lost relative to offering $S^*(\mu)$ to every customer. The inequality bounds it by the expected number of customers offered a nonoptimal assortment, and it is the first step of the regret bound at the end of the proof of Theorem 2.
--
--   **Formalization Note** The page writes it for $\pi_1$ with the generic symbol $\mathcal R^\pi$. It holds for every admissible policy and is stated so. Uniqueness of the optimum is not needed and is not assumed.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, p. 403, App. A, proof of Theorem 2, final display, first inequality

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel
import Definitions.Def_DynamicAssortment_Separation_History

namespace DynamicAssortment.Separation

/-- App. A, proof of Theorem 2, final display, first inequality (p. 403):
`ℛ^π(T, μ) ≤ ∑_{t=1}^T ℙ{NO(t)}`, `NO(t) = {S_t ≠ S*(μ)}`, for every admissible policy. -/
theorem regret_le_sum_prob_nonoptimal {N C T : ℕ} (hC : 1 ≤ C) (hCN : C ≤ N)
    (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (μ : Fin N → ℝ) (opt : (Fin N → ℝ) → Finset (Fin N))
    (hopt : IsOptimalSelection f w C opt)
    (π : Policy N T) (hπ : IsAdmissible C π) :
    regret f w μ (opt μ) π ≤ ∑ t : Fin T, prob f μ π (fun h => offeredAt π h t ≠ opt μ) := by sorry

end DynamicAssortment.Separation
