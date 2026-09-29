-- Prove2me | Theorems.Thm_BanditAlgorithm_exp3ix_pathwise_regret_decomposition
-- name    : BanditAlgorithm.exp3ix_pathwise_regret_decomposition
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-21T02:13:34.082753+00:00
-- url     : https://prove2.me/theorems/878049b0-45b9-4124-80a7-aa86dc8291e1
-- title:
--   Exp3-IX pathwise regret decomposition
-- statement:
--   This is the deterministic pathwise regret decomposition for Exp3-IX.
--
--   Let there be $k>1$ arms, let $x_{ti}\in[0,1]$ be the fixed reward table, let $\eta>0$, and let $h$ be a length-$n$ history whose observed rewards lie in $[0,1]$. Write $\widehat L_{n,i}$ for the Exp3-IX cumulative implicit-exploration loss estimate and $L_{n,i}=\sum_{t=1}^n(1-x_{ti})$ for arm $i$'s true cumulative loss. Then
--
--   $$
--   \widehat R_n \le \frac{\log k}{\eta}+\max_i(\widehat L_{n,i}-L_{n,i})+\eta\sum_i\widehat L_{n,i}.
--   $$
--
--   This is the deterministic half of the high-probability Exp3-IX analysis and is reusable independently of the concentration argument.
--
--   **Formalization Note** The theorem is stated pointwise for an arbitrary bounded history and specializes the source identity to $\gamma=\eta/2$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 12.1, printed p. 169 / PDF p. 178: combine Eq. (12.3) with Lemma 12.4 (the bias identity), then specialize gamma = eta/2.

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.exp3ix_pathwise_regret_decomposition
    {k : ℕ} (hk : 1 < k) (n : ℕ)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (h : BanditAlgorithm.BanditHistory k n)
    (hh : ∀ t : Fin n, (h t).2 ∈ Set.Icc (0 : ℝ) 1) :
    BanditAlgorithm.adversarialRandomRegret n x h ≤
      Real.log k / η +
        (⨆ i : Fin k,
          BanditAlgorithm.exp3IXEstimate η (η / 2) n h i -
            ∑ t : Fin n, (1 - x t i)) +
        η * ∑ i : Fin k, BanditAlgorithm.exp3IXEstimate η (η / 2) n h i := by
  sorry
