-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_lemma_6_6
-- name    : DynkinAsymInfo.Linear.lemma_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:34.332396+00:00
-- url     : https://prove2.me/theorems/075eb1cd-9e39-4637-ad16-68d4b49c6ba0
-- title:
--   Lemma 6.6 — type-one candidate is increasing
-- statement:
--   Let $0<A<B$, $\mu_0<0<\mu_1$, $\varepsilon>0$, and let $V_1$ be a $C^2$ solution on $[A,B]$ of all four equations in (81), including its constant values below $A$ and from $B$ onwards. Then
--   $$V_1'(\phi)\ge0\quad(\phi\in[A,B]),\qquad 1\le V_1(\phi)<1+\varepsilon\quad(\phi\in[A,B)).$$
--   The derivatives at $A$ and $B$ are taken from within $[A,B]$. The result locates the informed type's continuation and stopping regions.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, p. 22, Lemma 6.6, (81)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_Model

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, p. 22, Lemma 6.6,
with all four clauses of (81), p. 21. End derivatives are taken from [A,B]. -/
theorem lemma_6_6 (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (eps : ℝ) (heps : 0 < eps) (A B : ℝ) (hAB : 0 < A ∧ A < B)
    (v1 : ℝ → ℝ) (hC2 : ContDiffOn ℝ 2 v1 (Set.Icc A B))
    (hODE : ∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv v1) phi +
      (signalNoise p ^ 2 + p.sigma * signalNoise p) * phi * deriv v1 phi +
      p.mu1 * v1 phi = 0)
    (hleft : ∀ phi, 0 < phi → phi ≤ A → v1 phi = 1)
    (hright : ∀ phi, B ≤ phi → v1 phi = 1 + eps)
    (hB : derivWithin v1 (Set.Icc A B) B = 0) :
    (∀ phi ∈ Set.Icc A B, 0 ≤ derivWithin v1 (Set.Icc A B) phi) ∧
    (∀ phi ∈ Set.Icc A B, 1 ≤ v1 phi) ∧
    (∀ phi ∈ Set.Ico A B, v1 phi < 1 + eps) := by sorry

end DynkinAsymInfo.Linear
