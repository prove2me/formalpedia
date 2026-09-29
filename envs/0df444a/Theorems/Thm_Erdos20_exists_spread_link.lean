-- Prove2me | Theorems.Thm_Erdos20_exists_spread_link
-- name    : Erdos20.exists_spread_link
-- status  : Proved
-- author  : @lunjia
-- created : 2026-09-26T15:53:18.856621+00:00
-- url     : https://prove2.me/theorems/b5b254cf-de72-4ad3-a99b-3bd66c281104
-- title:
--   A large uniform family has a proper core with a spread link
-- statement:
--   Let $\mathcal F$ be a finite family of distinct $n$-element sets and let $R>1$. If $|\mathcal F|>R^n$, then there is a finite core $S$ such that
--
--   $$|S|<n,\qquad \operatorname{link}(\mathcal F,S)\ne\varnothing,$$
--
--   and the link is $R$-spread:
--
--   $$R^{|T|}\,|\{B\in\operatorname{link}(\mathcal F,S):T\subseteq B\}|\le|\operatorname{link}(\mathcal F,S)|\quad\text{for every finite }T.$$
--
--   The link consists of the sets $A\setminus S$ for $A\in\mathcal F$ containing $S$. Its members are therefore distinct and have positive size $n-|S|$. This isolates the deterministic core-extraction step used before the probabilistic disjoint-petals argument in logarithmic sunflower bounds.
-- source:
--   T. Tao, The sunflower lemma via Shannon entropy (20 July 2020), Lemma 2 (Locating the core), specialized to a family of distinct n-element sets with size > R^n: https://terrytao.wordpress.com/2020/07/20/the-sunflower-lemma-via-shannon-entropy/ .

import Definitions.Def_SunflowerSpread
import Mathlib.Data.Finset.Max

namespace Erdos20
theorem exists_spread_link {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (n : ℕ) (R : ℝ) (hR : 1 < R)
    (huni : ∀ A ∈ F, A.card = n) (hsize : R ^ n < (F.card : ℝ)) :
    ∃ S : Finset α, S.card < n ∧ (link F S).Nonempty ∧ IsSpread R (link F S) := by sorry
end Erdos20
