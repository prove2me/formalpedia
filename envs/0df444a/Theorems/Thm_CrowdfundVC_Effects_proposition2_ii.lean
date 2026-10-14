-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_proposition2_ii
-- name    : CrowdfundVC.Effects.proposition2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:44.556982+00:00
-- url     : https://prove2.me/theorems/e1ce664f-cbd3-4b47-8b47-fd36b2b988c9
-- title:
--   Proposition 2(ii), PDF p. 15 — if VC1 waits, it invests at t1 iff the signal is S and α ≥ R0/ẽ1|S
-- statement:
--   Under the standing assumptions ($0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta < 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, $\tilde e_1|S \ge R_0$), let $\alpha \in [0,1]$ be an equity share at which VC$_1$ does not invest at $t_0$. Then at $t_1$:
--
--   1. after the signal $F$, VC$_1$ does not invest: $\alpha\,\tilde e_1|F < R_0$;
--   2. after the signal $S$, VC$_1$ invests (its valuation $\alpha'\tilde e_1|S$ of the reduced share $\alpha' = (R_0-K)\alpha/R_0$ reaches the reduced requirement $R_0 - K$) if and only if
--   $$\alpha \ge \frac{R_0}{\tilde e_1|S}.$$
--
--   Together with Proposition 2(i), this describes VC$_1$'s whole strategy as a function of the offered share, which is what the startup anticipates when it chooses $\alpha$.
--
--   **Formalization Note** The hypotheses $\beta < 1$ and $0 \le R_f$ are added as for Proposition 2(i).
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF p. 15, Proposition 2(ii); proof Online Appendix D, PDF p. 50 (OA p. 23)

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- Proposition 2(ii) (p. 15). For `α ∈ [0, 1]`, if VC1 does not invest at `t0`, then at `t1` it
does not invest after the signal `F`, and it invests after the signal `S` if and only if `α ≥ R0/ẽ1|S`. -/
theorem proposition2_ii (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β < 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hI : P.R0 ≤ e1S P) :
    ∀ α : ℝ, 0 ≤ α → α ≤ 1 → ¬ investsAt0 P α →
      ¬ investsAfterF P α ∧ (investsAfterS P α ↔ P.R0 / e1S P ≤ α) := by sorry

end CrowdfundVC.Effects
