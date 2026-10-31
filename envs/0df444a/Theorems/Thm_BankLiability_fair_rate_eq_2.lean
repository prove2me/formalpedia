-- Prove2me | Theorems.Thm_BankLiability_fair_rate_eq_2
-- name    : BankLiability.fair_rate_eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:18.004038+00:00
-- url     : https://prove2.me/theorems/69e88000-f0e8-490a-b474-6e53add1fe21
-- title:
--   Eq. (2): $g^\circ$ makes the insurance contract worth zero and increases with $D$
-- statement:
--   Fix parameters in Table 1's ranges and an asset value $V>0$. For deposits $0\le D<(1-\beta)V$ let $V_b=D/(1-\beta)$, $q=(V_b/V)^\lambda$, and let $g^\circ$ be the fair assessment rate of (2),
--
--   $$g^\circ=\frac{r[\alpha-\beta]^+}{1-\beta}\Big[\frac{D/V}{1-\beta}\Big]^\lambda\Big(1-\Big[\frac{D/V}{1-\beta}\Big]^\lambda\Big)^{-1}.$$
--
--   1. At the rate $g^\circ$ the deposit insurance contract is worth zero to the insurer:
--   $$\frac{g^\circ D}{r}(1-q)-[D-(1-\alpha)V_b]^+\,q=0 .$$
--   2. If $D>0$, $g^\circ$ is the only rate $g$ for which the contract is worth zero.
--   3. $g^\circ$ is strictly increasing in $D$ on $[0,(1-\beta)V)$.
--
--   The first two clauses identify (2) as the fair premium: the present value of the premiums $g^\circ D$ paid until the regulator closes the bank at $V_b$ equals the present value of the insurer's loss at closure. The third is the paper's observation that a larger deposit base raises the assessment rate, which is the feedback channel from insurance cost to the bank's liability choice.
--
--   Differences from the source:
--   - reading: "the fair insurance premium should make the insurance contract worth zero" (contract value derived in the Online Appendix, not held) → the contract value is the closed form (g D/r)(1 − q) − [D − (1−α)V_b]⁺ q with q = (V_b/V)^λ; reason: premiums gD until closure at V_b and the loss [D − (1−α)V_b]⁺ at closure (p.5), priced with the model's state price (L/V)^λ
--   - reading: "the fair assessment rate" → g° makes the contract worth zero, and for D > 0 it is the only such rate (at D = 0 every rate does); reason: the definite article presupposes uniqueness, which holds exactly when D > 0
--   - encoding: formula (2) for deposits D → stated for 0 ≤ D < (1 − β)V; reason: (2) is undefined at D = (1 − β)V and negative deposits are not liability structures
-- source:
--   Sundaresan–Wang, Strategic Bank Liability Structure Under Capital Requirements, Management Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, §2.2, eq. (2) and the paragraph after it, p.5

import Mathlib
import Definitions.Def_BankLiability_Params
import Definitions.Def_BankLiability_lam
import Definitions.Def_BankLiability_Model

namespace BankLiability

/-- **Equation (2): g° is the fair assessment rate, and it increases with D.**
Sundaresan–Wang, *Strategic Bank Liability Structure Under Capital Requirements*, Management
Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, §2.2, eq. (2), p.5: "The fair
insurance premium should make the insurance contract worth zero to each party of the insurance
contract. [...] a closed-form formula of the fair assessment rate: g° = r[α−β]⁺/(1−β) ·
[D/V/(1−β)]^λ (1 − [D/V/(1−β)]^λ)^{−1}", and, same page, "Equation (2) indicates that the fair
assessment rate g° increases with D."

For asset value `V > 0` and deposits `0 ≤ D < (1 − β)V`:
1. at the rate g° of (2) the insurance contract is worth zero to the insurer
   (`insuranceValue P V D (fairRate P V D) = 0`);
2. for `D > 0`, g° is the only rate with this property;
3. g° is strictly increasing in `D` on `[0, (1 − β)V)`.

**Formalization Note.** The value of the insurance contract is its closed form at the state-price
level (`insuranceValue`: premiums `gD` until closure at V_b, against the loss
`[D − (1−α)V_b]⁺` at closure); the paper's derivation is in its Online Appendix. Strict
monotonicity uses β < α (Table 1). -/
theorem fair_rate_eq_2 (P : Params) (V : ℝ) (hV : 0 < V) :
    (∀ D : ℝ, 0 ≤ D → D < (1 - P.beta) * V → insuranceValue P V D (fairRate P V D) = 0) ∧
    (∀ D g : ℝ, 0 < D → D < (1 - P.beta) * V → insuranceValue P V D g = 0 →
      g = fairRate P V D) ∧
    StrictMonoOn (fun D => fairRate P V D) (Set.Ico 0 ((1 - P.beta) * V)) := by sorry

end BankLiability
