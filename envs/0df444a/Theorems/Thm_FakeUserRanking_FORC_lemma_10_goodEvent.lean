-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_lemma_10_goodEvent
-- name    : FakeUserRanking.FORC.lemma_10_goodEvent
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T07:05:35.738827+00:00
-- url     : https://prove2.me/theorems/d0d49f3b-83ef-4a03-a594-912311e3fb10
-- title:
--   Lemma 10, p. 30 — Expected Loss under Good Event G
-- statement:
--   **Lemma 10 (Upper Bounding Loss under Event $\mathcal G$).** There exists an absolute constant $C > 0$ such that for all $n \ge 1$, $T \ge 2$, $F \ge 0$, every instance with click probabilities $\mu_1 > \dots > \mu_n$ in $[0,1]$ and exit probabilities in $[0,1]$, every adaptive randomized fake-user policy $\mathbf P$ within fakeness budget $F$, and every resolution of FORC's tie-breaking and fallback rules,
--
--   $$\mathbb E\left[\mathbf 1_{\mathcal G}\sum_{j=1}^n\sum_{i=j+1}^n \Delta_{j,i}\sum_{t=1}^T \mathbf 1\{A_{r,t}(\pi_t(j)=i)\}\right] \le C\,\big(n^2 F + \log T\big)\sum_{j=1}^n\sum_{i=j+1}^n \frac{\log(nT)}{\Delta_{j,i}}.$$
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 30, Lemma 10 and App. D, pp. 56-62

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

open Classical in
/-- Lemma 10 (Upper Bounding Loss under Event G), p. 30: there is an absolute constant `C` such
that on the good event `G`, the expected weighted sum of sub-optimal feedback events is bounded by
`C (n²F + log T) ∑_{j<i} log(nT)/Δ_{j,i}`. -/
theorem lemma_10_goodEvent :
    ∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 2 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n),
        (∀ h k S, S.Nonempty → tb h k S ∈ S) →
      ∀ (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)),
        expect inst P (forc n T tb fb) T
          (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
            ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
              ∑ t : Fin T, (if feedbackEvent (forc n T tb fb) τ t j i then 1 else 0)) ≤
          C * (((n : ℝ) ^ 2 * F + Real.log T) *
            ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i) := by sorry

end FakeUserRanking.FORC
