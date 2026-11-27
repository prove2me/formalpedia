-- Prove2me | Theorems.Thm_AssortOpt_HMF_Supplement_theorem_4
-- name    : AssortOpt.HMF.Supplement.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:21:59.022611+00:00
-- url     : https://prove2.me/theorems/8c53e433-8a57-4a09-8428-077cd4235c0b
-- title:
--   Theorem 4 — on a geometric-price family the top-2 lottery earns n/2 while assortments earn at most n/e + O(log n)
-- statement:
--   Fix $M$ and consider the family of Theorem 4 (definition `TopTwoFamily`): $n$ items with prices $r_j=M^j$, buyer lists of length at most two whose most expensive item is $j$ with probability $M^{-j}$, the item $j>1$ being the second choice after a first choice uniform on $\{1,\dots,j-1\}$. Let $x^{(2)}$ be the top-2 lottery ($w_j=1/2$, $B=1$). There is a threshold $M_0$ such that for every $M\ge M_0$:
--
--   1. on every instance, $\mathsf{REV}[x^{(2)}]\ge n/2$;
--   2. there are $C$ and $N$ such that for every $n\ge N$, every instance with $n$ items and every assortment $S$,
--   $$\mathsf{REV}[S]\le \frac ne+C\log n;$$
--   3. for every $\varepsilon>0$ there is $N$ such that for every $n\ge N$, every instance and every assortment $S$, $\mathsf{REV}[S]\le(2/e+\varepsilon)\,\mathsf{REV}[x^{(2)}]$.
--
--   Together with Theorem 3 this places the worst-case ratio between the best assortment and the best budget-additive mechanism in $[1/e,2/e]$.
--
--   Differences from the source:
--   - reading: 'M denotes a fixed large constant' → ∃ M₀, ∀ M ≥ M₀ (every clause holds for every sufficiently large fixed M); reason: the source gives no threshold; 'fixed large' means for all M beyond some threshold, and the constants of the O(log n) clause may depend on the fixed M
--   - encoding: as n → ∞, no assortment earns more than n/e + O(log n) → ∃ C N, ∀ n ≥ N, every instance D with n items, ∀ S, REV[S] ≤ n/e + C log n; reason: the standard meaning of an O(log n) bound as n → ∞, with the threshold N present
--   - generalization: assortments obtain no more than 2/e times the revenue of the best budget-additive mechanism in the worst case → ∀ ε > 0, ∃ N, ∀ n ≥ N, every instance, ∀ S: REV[S] ≤ (2/e + ε) · REV[top-2 lottery]; reason: the top-2 lottery is budget-additive, so its revenue is at most the best budget-additive revenue; the Lean ratio bound against the top-2 lottery (the comparison made in the proof, p. 56) implies the source's
--   - encoding: items 1, …, n, prices M^j and the verbal description of the list distribution → 0-based Fin n, thm4Price M i = M^(i+1), and IsThm4Instance M D fixing the positive support and the weights of D to thm4Prob M; reason: the same distribution; the instance is characterized by hypotheses rather than constructed, which excludes no instance
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 25, Theorem 4

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_TopTwoFamily

namespace AssortOpt.HMF.Supplement

theorem theorem_4 :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M →
      (∀ (n : ℕ) (D : ListDist n), IsThm4Instance M D →
          (n : ℝ) / 2 ≤ revMech D (thm4Price M) topTwoLottery) ∧
      (∃ (C : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n → ∀ D : ListDist n, IsThm4Instance M D →
          ∀ S : Finset (Fin n),
            revAssort D (thm4Price M) S ≤ (n : ℝ) / Real.exp 1 + C * Real.log n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ D : ListDist n, IsThm4Instance M D →
          ∀ S : Finset (Fin n),
            revAssort D (thm4Price M) S ≤
              (2 / Real.exp 1 + ε) * revMech D (thm4Price M) topTwoLottery) := by sorry

end AssortOpt.HMF.Supplement
