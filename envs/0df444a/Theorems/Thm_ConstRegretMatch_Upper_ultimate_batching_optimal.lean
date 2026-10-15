-- Prove2me | Theorems.Thm_ConstRegretMatch_Upper_ultimate_batching_optimal
-- name    : ConstRegretMatch.Upper.ultimate_batching_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:57.85574+00:00
-- url     : https://prove2.me/theorems/0d4408ea-c9eb-41fa-9475-f2e93c35804f
-- title:
--   §2, p. 8 — 𝓡^{*,t} = max_{D∈Π} 𝓡^{D,t}, attained by the ultimate batching policy
-- statement:
--   Fix a matching network with values $r_m>0$ and arrival probabilities $\lambda$, and a horizon $t\in\mathbb N$. Then the hindsight benchmark
--   $$\mathcal R^{*,t}=\mathbb E\big[\max\{r\cdot y: My\le A^t,\ y\in\mathbb Z^d_{\ge0}\}\big]$$
--   satisfies:
--
--   1. $\mathcal R^{D,t}\le\mathcal R^{*,t}$ for every admissible matching policy $D$;
--   2. some admissible policy $D$ has $\mathcal R^{D,t}=\mathcal R^{*,t}$.
--
--   Hence $\mathcal R^{*,t}=\max_{D\in\Pi}\mathcal R^{D,t}$. The policy attaining it waits until time $t$ and then performs an optimal solution of the static weighted matching problem at time $t$ (the ultimate batching policy).
--
--   This identifies the benchmark of the regret, defined as the expected static optimum, with the paper's definition as the best value any admissible policy can collect by a fixed time.
--
--   **Formalization Note** Admissible policies are defined in `Policy`: no rejections, non-anticipative, and matching only agents present. The statement holds for each fixed $t$; the attaining policy may depend on $t$.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), pp. 8–9, §2 (Performance measure)

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP
import Definitions.Def_ConstRegretMatch_Upper_Arrivals
import Definitions.Def_ConstRegretMatch_Upper_Policy

namespace ConstRegretMatch.Upper

/-- §2, p. 8: for every horizon `t`, no admissible policy collects more expected value by time `t`
than the hindsight benchmark `𝓡^{*,t} = 𝔼[max {r · y : M y ≤ A^t}]`, and some admissible policy
(the ultimate batching policy) collects exactly `𝓡^{*,t}`; i.e. `𝓡^{*,t} = max_{D ∈ Π} 𝓡^{D,t}`. -/
theorem ultimate_batching_optimal {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : IsMatchValues r) (lam : Fin n → ℝ) (hlam : IsArrivalRates lam) (t : ℕ) :
    (∀ D : Policy n d, IsAdmissible N D → valueOf lam r D t ≤ Rstar N lam r t) ∧
      ∃ D : Policy n d, IsAdmissible N D ∧ valueOf lam r D t = Rstar N lam r t := by sorry

end ConstRegretMatch.Upper
