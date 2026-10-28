-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_lemma_10_pair
-- name    : FakeUserRanking.FORC.lemma_10_pair
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T07:16:29.794998+00:00
-- url     : https://prove2.me/theorems/8cee71c3-e2bb-47a3-ac82-69078b766ba5
-- title:
--   Lemma 10, p. 30 — Per-Pair Expected Sub-Optimal Feedback Count under Good Event G
-- statement:
--   **Lemma 10 (Per-Pair Bound under Event $\mathcal G$, p. 30).** There exists an absolute constant $C > 0$ such that for all $n \ge 1$, $T \ge 2$, $F \ge 0$, every instance with strictly decreasing click probabilities $\mu_1 > \dots > \mu_n$, every policy $\mathbf P$ within fakeness budget $F$, every resolution of FORC's tie-breaking and fallback rules, and every pair of products $j < i$,
--
--   $$\mathbb E\left[\mathbf 1_{\mathcal G}\sum_{t=1}^T \mathbf 1\{A_{r,t}(\pi_t(j)=i)\}\right] \le C\,\big(n^2 F + \log T\big)\,\frac{\log(nT)}{\Delta_{j,i}^2}.$$
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 30, Lemma 10 and App. D, pp. 56-62

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

open Classical in
/-- Lemma 10 (Per-Pair Bound, p. 30 and App. D, pp. 56–62): there is an absolute constant `C` such
that for every pair of products `j < i`, the expected number of rounds on event `G` in which
`feedbackEvent` occurs for `(j, i)` is at most `C (n²F + log T) log(nT) / Δ_{j,i}²`. -/
theorem lemma_10_pair :
    ∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 2 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n),
        (∀ h k S, S.Nonempty → tb h k S ∈ S) →
      ∀ (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)),
      ∀ (j i : Fin n), j < i →
        expect inst P (forc n T tb fb) T
          (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
            ∑ t : Fin T, (if feedbackEvent (forc n T tb fb) τ t j i then 1 else 0)) ≤
          C * (((n : ℝ) ^ 2 * F + Real.log T) *
            (Real.log ((n : ℝ) * T) / gap inst j i ^ 2)) := by sorry

end FakeUserRanking.FORC
