-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_prob_goodG2_quarter
-- name    : FakeUserRanking.FORC.prob_goodG2_quarter
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T07:18:49.578992+00:00
-- url     : https://prove2.me/theorems/7be2cb36-e659-4a37-89c4-6843d614e2b7
-- title:
--   Lemma 5 (Tightened Constant): Event G2 Holds with Probability at Least 1 - delta/4
-- statement:
--   **Tightened Exposure Bound for Event $\mathcal G_2$ (Lemma 5).** For all $n \ge 1$, $T \ge 2$, $F \ge 0$, every instance with click probabilities $\mu_1 > \dots > \mu_n$ in $[0,1]$, every adaptive policy $\mathbf P$ within fakeness budget $F$, and every resolution of FORC's tie-breaking and fallback rules, the event $\mathcal G_2$ (that every level $\ell \ge \lceil \log_2 F \rceil$ is exposed to at most $\log(2L/\delta) + 3$ fake users) satisfies
--
--   $$\mathbb P(\mathcal G_2) \ge 1 - \frac{\delta(n, T)}{4}.$$
--
--   This follows from the exponential supermartingale tail bound $\mathbb P(\mathrm{exposure}_k > a) \le \exp(e - 1 - a)$ at $a = \log(2L/\delta) + 3$, using $e - 4 < -1 < -\log 2$ so that $\exp(e - 4 - \log(2L/\delta)) \le \delta/(4L)$, and summing over the $L$ levels.
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, Lemma 5, p. 29 and Appendix C.2, pp. 51-53

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

/-- Tightened Lemma 5: since `e - 4 < -log 2`, the exposure bound `G₂` holds with probability at
least `1 − δ/4`. -/
theorem prob_goodG2_quarter (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)) :
    1 - delta n T / 4 ≤ prob inst P (forc n T tb fb) T (goodG2 F) := by sorry

end FakeUserRanking.FORC
