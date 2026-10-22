-- Prove2me | Theorems.Thm_AdInterm_SPE_lemma_2_1_A
-- name    : AdInterm.SPE.lemma_2_1_A
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:14.427761+00:00
-- url     : https://prove2.me/theorems/c36b5b87-9965-4d90-80be-05b88c7f3d4f
-- title:
--   Lemma 2.1(A), p. 14 — every agent other than the seller faces an upstream threshold equivalent to a second-price auction
-- statement:
--   Consider the symmetric $k$-tree with $k_t\ge1$ for $t=1,\dots,n+1$. Suppose every intermediary uses a mechanism in $\mathcal M$ and the seller runs a second-price auction with reserve $r_S\ge0$. Fix any agent $I_{(t,j)}$ other than the seller ($0\le t\le n$; buyers included).
--
--   Then there is a threshold $T(v)\in[0,\infty]$, a function of the buyers' values $v$ that does not depend on the values of the buyers below $I_{(t,j)}$, such that for every report $b\ge0$ of $I_{(t,j)}$ (all other agents' reports fixed):
--
--   $$
--   b>T(v)\ \Rightarrow\ I_{(t,j)}\text{ wins},\qquad I_{(t,j)}\text{ wins with }b\ \Rightarrow\ b\ge T(v),
--   $$
--
--   and whenever $I_{(t,j)}$ wins, its payment equals $T(v)$.
--
--   So the upstream mechanism faced by $I_{(t,j)}$ acts, in allocation and payment, like a second-price auction whose reserve and random competing bid combine into $T(v)$. This is the reduction that lets Lemma 3.1 be applied at every tier.
--
--   **Formalization Note** The page's "equivalent in terms of payments and allocations" cannot hold exactly at a tie $b=T(v)$, which any single-winner allocation must break (here: toward the lowest index); the statement is therefore made on either side of the threshold, which holds for every tie rule. $T(v)=\infty$ means the agent cannot win. The explicit formulas of the page's proof for the competing bid and reserve agree with $T$ off ties and jumps of the reporting functions, and are not asserted.
-- source:
--   Balseiro, Candogan & Gurkan, Multi-stage Intermediation in Display Advertising, SSRN 2661459 (manuscript of 2019-08-17; M&SOM doi:10.1287/msom.2019.0854), Lemma 2.1(A), p. 14; proof p. 34; Definition A.1, p. 41

import Mathlib
import Definitions.Def_AdInterm_SPE_Setting

open MeasureTheory

namespace AdInterm.SPE

theorem lemma_2_1_A (n : ℕ) (k : ℕ → ℕ)
    (hk : ∀ t, 1 ≤ t → t ≤ n + 1 → 1 ≤ k t)
    (σ : Profile)
    (hσ : ∀ s i, 1 ≤ s → s ≤ n → IsMech (σ s i))
    (rS : ℝ) (hrS : 0 ≤ rS)
    (t j : ℕ) (ht : t ≤ n) (hj : j < nodes k n t) :
    ∃ T : (ℕ → ℝ) → WithTop ℝ,
      (∀ v v', (∀ i, ¬ DescendantBuyer k t j i → v i = v' i) → T v = T v') ∧
      (∀ v (b : ℝ), 0 ≤ b →
        (T v < (b : WithTop ℝ) → winsWith k n σ rS v t j b) ∧
        (winsWith k n σ rS v t j b → T v ≤ (b : WithTop ℝ))) ∧
      (∀ v, wins k n σ rS v t j → (pay k n σ rS v t j : WithTop ℝ) = T v) := by sorry

end AdInterm.SPE
