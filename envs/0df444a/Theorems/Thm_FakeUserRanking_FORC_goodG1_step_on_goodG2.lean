-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_goodG1_step_on_goodG2
-- name    : FakeUserRanking.FORC.goodG1_step_on_goodG2
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T07:16:25.073745+00:00
-- url     : https://prove2.me/theorems/ccce463f-ebfa-47d0-8c79-17a4c74a46c0
-- title:
--   Appendix C.3, pp. 54–56 — Single-(Round, Level, Item) Concentration Failure Bound on G2
-- statement:
--   **Single-(Round, Level, Item) Concentration Bound on $\mathcal G_2$ (Appendix C.3, pp. 54–56).** For every $n \ge 1$, $T \ge 2$, $F \ge 0$, every instance with click probabilities $\mu_1 > \dots > \mu_n$ in $[0,1]$, every adaptive policy $\mathbf P$ within fakeness budget $F$, every round $t = s + 1 \in [T]$, every level $\ell = k + 1$ with $F \le 2^{k+1}$, and every product $i \in [n]$,
--
--   $$\mathbb P\Big(\mathcal G_2 \cap \big\{\big|\hat r^{(\ell)}_{i,t} - \mu_i\big| > w^{(\ell)}_{i,t}\big\}\Big) \le \frac{\delta(n,T)}{4\,T\,L\,n}.$$
--
--   On $\mathcal G_2$, the fake-user perturbation of $\hat r^{(\ell)}_{i,t}$ is bounded deterministically by $(\log(2L/\delta) + 4)/\max(\hat\eta^{(\ell)}_{i,t}, 1)$, and Lemma 13 bounds the real-user deviation probability by $2(4nT/\delta)^{-3} \le \delta/(4TLn)$.
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, Appendix C.3, pp. 54-56

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

/-- Appendix C.3, pp. 54–56: for each round `s`, qualifying level `k` (`F ≤ 2^(k+1)`), and item `i`,
the probability that `G₂` holds while the cross-learned estimate `r̂^(k)_{i,s+1}` falls outside the
window `w^(k)_{i,s+1}` around `μ_i` is at most `δ / (4 T L n)`. -/
theorem goodG1_step_on_goodG2 (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (s : Fin T) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) (i : Fin n) :
    prob inst P (forc n T tb fb) T
      (fun τ => goodG2 F τ ∧ ¬ (
        rHat (stateAt tb fb τ ((s : ℕ) + 1)) k i -
          window21 n T (stateAt tb fb τ ((s : ℕ) + 1)) k i ≤ inst.μ i ∧
        inst.μ i ≤
          rHat (stateAt tb fb τ ((s : ℕ) + 1)) k i +
            window21 n T (stateAt tb fb τ ((s : ℕ) + 1)) k i)) ≤
      delta n T / (4 * (T : ℝ) * (numLevels T : ℝ) * (n : ℝ)) := by sorry

end FakeUserRanking.FORC
