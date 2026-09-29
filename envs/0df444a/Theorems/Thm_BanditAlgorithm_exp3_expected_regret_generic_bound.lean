-- Prove2me | Theorems.Thm_BanditAlgorithm_exp3_expected_regret_generic_bound
-- name    : BanditAlgorithm.exp3_expected_regret_generic_bound
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-07-18T16:28:07.910133+00:00
-- url     : https://prove2.me/theorems/5211c961-7b9c-4a48-b638-99a44093c393
-- title:
--   Exp3 generic expected-regret bound
-- statement:
--   For an adversarial $k$-armed bandit with rewards in $[0,1]$, horizon $n\ge 1$, and an Exp3 policy with any positive learning rate $\eta$, the expected regret satisfies $$R_n(\pi,x)\le \frac{\log k}{\eta}+\frac{\eta n k}{2}.$$ This is the pre-optimization estimate obtained by taking expectations in Eq. (11.15).
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Theorem 11.2 proof, printed pp. 156–157, especially Eq. (11.15) and the expectation calculation immediately following it. https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem exp3_expected_regret_generic_bound
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hη : 0 < η) (hπ : IsExp3Policy η π) :
    adversarialRegret n x π ≤ Real.log k / η + η * n * k / 2 := by
  sorry

end BanditAlgorithm
