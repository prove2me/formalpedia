-- Prove2me | Theorems.Thm_DelayedSWPT_Extended_exists_sigmaE
-- name    : DelayedSWPT.Extended.exists_sigmaE
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:09:44.831425+00:00
-- url     : https://prove2.me/theorems/4057d38c-bfb0-41d5-85f7-a38af4562034
-- title:
--   Inequality (1) holds for the constructed schedule $\sigma_E$
-- statement:
--   Let (P) be an instance, (2P) its doubled problem, (E) its extended problem with gap jobs $G$, and $\pi_E$ the schedule of (E) induced by Delayed SWPT. For every optimal schedule $\mu^*$ of (2P) there is a feasible schedule $\sigma_E$ of (E) with
--
--   $$\sum_{j\in J} w_j C_j(\sigma_E) + \sum_{g\in G} w_g C_g(\sigma_E) \le \sum_{j\in J} w_j C_j(\mu^*) + \sum_{g\in G} w_g C_g(\pi_E). \tag{1}$$
--
--   In the paper, $\sigma_E$ ends each nongap job $j$ at its completion time in $\mu^*$, inserts the gap jobs block by block as early as possible, and shifts the gap-generating jobs left; Lemmas 4–7 bound the resulting change in cost. Together with Lemma 3 this proves the upper half of Theorem 8.
--
--   **Formalization Note** The statement is existential, so the construction of $\sigma_E$ is left to the prover. In (2P), $C_j(\mu^*) = \mu^*_j + 2p_j$; for a gap job $g_t$, $C_g(\pi_E) = t + 1$.
-- source:
--   Anderson and Potts, Online Scheduling of a Single Machine to Minimize Total Weighted Completion Time, Math. Oper. Res. 29(3) (2004), pp. 692–696, §§3.4–3.6, proof of Theorem 8, inequality (1)

import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

namespace DelayedSWPT.Extended

open DelayedSWPT.Model

/-- Anderson and Potts (2004), §§3.4–3.6, proof of Theorem 8, p. 696: from an optimal schedule
`μ*` of (2P) one can construct a feasible schedule `σ_E` of (E) satisfying inequality (1)
`∑_{j∈J} wⱼ Cⱼ(σ_E) + ∑_{g∈G} w_g C_g(σ_E) ≤ ∑_{j∈J} wⱼ Cⱼ(μ*) + ∑_{g∈G} w_g C_g(π_E)`. -/
theorem exists_sigmaE {n : ℕ} (I : Instance n) (μstar : Fin n → ℕ)
    (hμ : IsOptimal (double I).r (double I).p (double I).w μstar) :
    ∃ σE : EJob I → ℕ, IsFeasible (rE I) (pE I) σE ∧
      ∑ j : Fin n, I.w j * ((σE (Sum.inl j) + I.p j : ℕ) : ℝ) +
          ∑ g : gapTimes I, gapWeight I g * ((σE (Sum.inr g) + 1 : ℕ) : ℝ) ≤
        ∑ j : Fin n, I.w j * ((μstar j + 2 * I.p j : ℕ) : ℝ) +
          ∑ g : gapTimes I, gapWeight I g * ((g.1 + 1 : ℕ) : ℝ) := by sorry

end DelayedSWPT.Extended
