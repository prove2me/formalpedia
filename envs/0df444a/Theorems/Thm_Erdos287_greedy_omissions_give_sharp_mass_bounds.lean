-- Prove2me | Theorems.Thm_Erdos287_greedy_omissions_give_sharp_mass_bounds
-- name    : Erdos287.greedy_omissions_give_sharp_mass_bounds
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T06:27:51.021257+00:00
-- url     : https://prove2.me/theorems/5952b125-a571-5192-8f9e-570e1f6844be
-- title:
--   Greedy omissions give sharp retained mass bounds with forced positions
-- statement:
--   Let $I$ be a finite set of integer positions with nonnegative nonincreasing weights $w(n)$. Let $H\subseteq I$ be required omissions and let $R$ be positions that must be retained. Suppose $H$ is disjoint from $R$ and contains no consecutive pair. Among omission sets $T$ with $H\subseteq T\subseteq I$, disjoint from $R$ and containing no consecutive pair, the retained mass has a minimum attained by the following greedy choice. Start with $H$. In the remaining eligible positions, omit the smallest available position, skip its successor, and continue. The maximum retained mass is obtained by omitting just $H$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Sharp mass bounds in a finite interval under arithmetic omissions and the spacing constraint.

import Mathlib

theorem Erdos287.greedy_omissions_give_sharp_mass_bounds (I H R : Finset ℕ) (w : ℕ → ℚ)
    (hH : H ⊆ I) (hdisj : Disjoint H R)
    (hsep : ∀ n ∈ H, n + 1 ∉ H)
    (hw : ∀ a ∈ I, ∀ b ∈ I, a ≤ b → w b ≤ w a)
    (hnonneg : ∀ n ∈ I, 0 ≤ w n) :
    ∃ G : Finset ℕ, H ⊆ G ∧ G ⊆ I ∧ Disjoint G R ∧
      (∀ n ∈ G, n + 1 ∉ G) ∧
      ∀ T : Finset ℕ, H ⊆ T → T ⊆ I → Disjoint T R →
        (∀ n ∈ T, n + 1 ∉ T) →
        (∑ n ∈ I \ G, w n) ≤ (∑ n ∈ I \ T, w n) ∧
          (∑ n ∈ I \ T, w n) ≤ ∑ n ∈ I \ H, w n := by sorry
