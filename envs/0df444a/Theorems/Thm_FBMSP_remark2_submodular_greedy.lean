-- Prove2me | Theorems.Thm_FBMSP_remark2_submodular_greedy
-- name    : FBMSP.remark2_submodular_greedy
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T11:46:39.538152+00:00
-- url     : https://prove2.me/theorems/5e991052-4b34-44e6-af53-78a6ddf192fb
-- title:
--   Remark 2 — Submodular menus and greedy approximation
-- statement:
--   Expected menu revenue is zero for the empty set, nonnegative, monotone under inclusion, and submodular:
--   $$F(A\cap B)+F(A\cup B)\le F(A)+F(B).$$
--   For any finite nonnegative candidate menu $P$ and $0\le k\le|P|$, a greedy chain exists. Every such chain ends at a feasible $k$-element menu $G_k\subseteq P$ satisfying
--   $$F(G_k)\ge(1-e^{-1})\max_{A\subseteq P,\ |A|\le k}F(A).$$
--   The optimum in this target is explicitly over $P$. The separate discrete candidate-price target recovers the unrestricted finite-support pricing problem. No unconditional polynomial-time claim is made for an arbitrarily specified continuous error distribution.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Remark 2, p.15; Appendix C, pp.50–51 (ec16–ec17).

import Definitions.Def_FBMSP_Model

namespace FBMSP

/-- Remark 2: expected menu revenue is a normalized nonnegative monotone
submodular set function.  Greedy selection over a finite candidate menu
achieves at least 1-exp(-1) times the best k-element candidate sub-menu.
The benchmark here is explicitly the finite-candidate optimum.
Draft statement; proof remains open. -/
theorem remark2_submodular_greedy (ν η : MeasureTheory.Measure ℝ)
    (hpred : ValidPredictions ν) (hnoise : ValidNoise η) :
    menuRevenue ν η ∅ = 0 ∧
    (∀ P : Finset ℝ, 0 ≤ menuRevenue ν η P) ∧
    Monotone (menuRevenue ν η) ∧
    IsSubmodular (menuRevenue ν η) ∧
    ∀ (P : Finset ℝ) (k : ℕ), k ≤ P.card → (∀ p ∈ P, 0 ≤ p) →
      (∃ A : ℕ → Finset ℝ, IsGreedyChain (menuRevenue ν η) P k A) ∧
      ∀ A : ℕ → Finset ℝ, IsGreedyChain (menuRevenue ν η) P k A →
        A k ⊆ P ∧ (A k).card = k ∧
          (1 - Real.exp (-1)) * candidateOptimum (menuRevenue ν η) P k ≤
            menuRevenue ν η (A k) := by sorry

end FBMSP
