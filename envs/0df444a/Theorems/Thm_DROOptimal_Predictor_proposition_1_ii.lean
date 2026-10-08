-- Prove2me | Theorems.Thm_DROOptimal_Predictor_proposition_1_ii
-- name    : DROOptimal.Predictor.proposition_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:40.151991+00:00
-- url     : https://prove2.me/theorems/fb25b363-96c0-43c0-9514-a2ed1aa2b9e5
-- title:
--   Proposition 1(ii), p. 12 — joint convexity of the relative entropy I(ℙ′,ℙ) on 𝒫 × 𝒫
-- statement:
--   Let $\mathcal P$ be the probability simplex on $\Xi=\{1,\dots,d\}$ and $I(\mathbb P',\mathbb P)\in[0,\infty]$ the relative entropy of $\mathbb P'$ with respect to $\mathbb P$ (Definition 5, with $p'\log(p'/0)=+\infty$ for $p'>0$). For all pairs $(\mathbb P_1',\mathbb P_1),(\mathbb P_2',\mathbb P_2)\in\mathcal P\times\mathcal P$ and every $\lambda\in[0,1]$,
--   $$
--   I\big((1-\lambda)\mathbb P_1'+\lambda\mathbb P_2',\ (1-\lambda)\mathbb P_1+\lambda\mathbb P_2\big)\le(1-\lambda)\,I(\mathbb P_1',\mathbb P_1)+\lambda\, I(\mathbb P_2',\mathbb P_2).
--   $$
--
--   The proof of Theorem 4 uses this with $\mathbb P_1'=\mathbb P_2'$, to move a model along a segment while keeping its relative entropy distance from the observed frequencies below $r$.
--
--   **Formalization Note** Both sides are computed in `EReal`, where $0\cdot(+\infty)=0$; so at $\lambda=0$ (or $\lambda=1$) an infinite term multiplied by zero does not contribute, as in the usual convention of convex analysis.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 12, Proposition 1(ii)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Predictor_Problem5

namespace DROOptimal.Predictor

/-- Proposition 1(ii) (Convexity), p. 12: for all pairs (ℙ′₁, ℙ₁), (ℙ′₂, ℙ₂) ∈ 𝒫 × 𝒫 and
λ ∈ [0, 1],
I((1 − λ)ℙ′₁ + λℙ′₂, (1 − λ)ℙ₁ + λℙ₂) ≤ (1 − λ) I(ℙ′₁, ℙ₁) + λ I(ℙ′₂, ℙ₂),
in `EReal` (where 0 · ∞ = 0). -/
theorem proposition_1_ii {d : ℕ} (ℙ'₁ ℙ₁ ℙ'₂ ℙ₂ : Δ d) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    relEntropy (mix t ht ℙ'₁ ℙ'₂) (mix t ht ℙ₁ ℙ₂) ≤
      ((1 - t : ℝ) : EReal) * relEntropy ℙ'₁ ℙ₁ + ((t : ℝ) : EReal) * relEntropy ℙ'₂ ℙ₂ := by sorry

end DROOptimal.Predictor
