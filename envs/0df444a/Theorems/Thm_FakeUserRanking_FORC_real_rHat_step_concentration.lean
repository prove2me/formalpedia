-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_real_rHat_step_concentration
-- name    : FakeUserRanking.FORC.real_rHat_step_concentration
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T07:55:23.979879+00:00
-- url     : https://prove2.me/theorems/7b24e5ab-c86b-465f-819e-b43e068bff71
-- title:
--   Appendix C.3, Eqs. (42)–(43) — Real-User Cross-Learned Reward Concentration at a Single Step
-- statement:
--   **Real-User Cross-Learned Reward Concentration (Appendix C.3, Eqs. 42–43, pp. 55–56).** For all $n \ge 1$, $T \ge 2$, $F \ge 0$, every instance with strictly decreasing click probabilities $\mu_1 > \dots > \mu_n$, every policy $\mathbf P$ within fakeness budget $F$, every resolution of FORC's tie-breaking and fallback rules, and every round $s \in [T]$, qualifying level $k$ ($F \le 2^{k+1}$), and product $i \in [n]$, let $\hat{\eta}^{(k)}_{r,i,s+1}$ and $\hat{C}^{(k)}_{r,i,s+1}$ denote the cross-learned feedback count and click count contributed by real users up to round $s$. Then
--
--   $$\mathbb P\left(\hat{\eta}^{(k)}_{r,i,s+1} > 0 \;\wedge\; \left|\frac{\hat{C}^{(k)}_{r,i,s+1}}{\hat{\eta}^{(k)}_{r,i,s+1}} - \mu_i\right| > \sqrt{\frac{\frac{3}{2}\log(4nT/\delta)}{\hat{\eta}^{(k)}_{r,i,s+1}}}\right) \le \frac{\delta}{4 T L n}.$$
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar (2023), Learning Product Rankings Robust to Fake Users, Appendix C.3, Eqs. (42)-(43), pp. 55-56

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

open Classical in
/-- Real-user cross-learned reward concentration (Appendix C.3, Eqs. 42–43, pp. 55–56): at the end of
round `s`, for level `k` and product `i`, the probability that the real-user cross-learned feedback
count `etaHatR` is positive and the real-user cross-learned average reward `clkHatR / etaHatR`
deviates from `μ_i` by more than `√((3/2) log(4nT/δ) / etaHatR)` is at most `δ / (4 T L n)`. -/
theorem real_rHat_step_concentration (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (s : Fin T) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) (i : Fin n) :
    prob inst P (forc n T tb fb) T
      (fun τ =>
        let cntR (g : Fin (numLevels T)) : ℝ :=
          ∑ t : Fin T, if t ≤ s ∧ (τ t).1 = g ∧ (τ t).2.1 = none ∧
            (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1 then 1 else 0
        let clkR (g : Fin (numLevels T)) : ℝ :=
          ∑ t : Fin T, if t ≤ s ∧ (τ t).1 = g ∧ (τ t).2.1 = none ∧
            (τ t).2.2.2 = true ∧ i = ranking (forc n T tb fb) τ t (τ t).2.2.1 then 1 else 0
        let etaHatR : ℝ :=
          (∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < k), cntR g) /
            2 ^ ((k : ℕ) + 1) + cntR k
        let clkHatR : ℝ :=
          (∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < k), clkR g) /
            2 ^ ((k : ℕ) + 1) + clkR k
        0 < etaHatR ∧
          Real.sqrt ((3 / 2) * Real.log (4 * (n : ℝ) * T / delta n T) / etaHatR) <
            |clkHatR / etaHatR - inst.μ i|) ≤
      delta n T / (4 * (T : ℝ) * (numLevels T : ℝ) * (n : ℝ)) := by sorry

end FakeUserRanking.FORC
