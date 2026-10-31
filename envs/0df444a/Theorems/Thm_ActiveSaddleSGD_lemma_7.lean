-- Prove2me | Theorems.Thm_ActiveSaddleSGD_lemma_7
-- name    : ActiveSaddleSGD.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:14.799404+00:00
-- url     : https://prove2.me/theorems/26ec1f0d-4902-4622-92b7-69a24f77ba40
-- title:
--   Lemma 7 — $F(w)=(-J^-+\Delta(w))w^-$ with $\Delta(w)=O(\|w\|)$
-- statement:
--   Let $\mathcal U$, $G$ be as in Proposition 6 and $F$ as on p.26. There is a function $\Delta:\mathbb R^d\to\mathbb R^{d^-\times d^-}$ such that $\Delta(w)=O(\|w\|)$ and, near $0$,
--   $$
--   F(w)=F(w^+,w^-)=(-J^-+\Delta(w))w^-.
--   $$
--
--   So the recursion for $w^-$ is, near the origin, a linear repulsion from the center-stable graph.
--
--   **Formalization Note** $\Delta(w)=O(\|w\|)$ reads: there are $C,\delta>0$ with $\|\Delta(w)\|\le C\|w\|$ for $\|w\|<\delta$.
--
--   Differences from the source:
--   - reading: $F(w)=(-J^-+\Delta(w))w^-$, unqualified → the identity on the ball $\|w\|<\delta$; reason: the proof, (21), needs $w^+\in\mathcal U$, and $F(w^+,0)=0$ is false in general for $w^+\notin\mathcal U$
--   - encoding: $G$ with the extension of Remark 5 → $G$ any graph of Proposition 6; reason: only $G$ near $0$ matters; the extended $G$ is an instance
--   - encoding: $\mathbb R^d$ in the basis of $P$ → $\mathbb R^{d^+}\times\mathbb R^{d^-}$ with the product norm; reason: the $O(\cdot)$ does not depend on the norm
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Lemma 7, p.26

import Mathlib
import Definitions.Def_ActiveSaddleSGD_CenterStable

namespace ActiveSaddleSGD

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Lemma 7, p.26: there is a function
`Δ : ℝᵈ → ℝ^{d⁻×d⁻}` with `Δ(w) = O(‖w‖)` and `F(w) = F(w⁺, w⁻) = (−J⁻ + Δ(w)) w⁻`.

**Formalization Note** `Δ(w) = O(‖w‖)` is at `0`: `‖Δ(w)‖ ≤ C ‖w‖` for `‖w‖ < δ`. The identity is stated
on that ball, the only place the proof gives it ((21) needs `w⁺ ∈ 𝒰`): `F(w⁺, 0) = 0` is false in
general for `w⁺ ∉ 𝒰`. `G` is any graph of Proposition 6, with or without the extension of Remark 5. -/
theorem lemma_7 {dp dm : ℕ} (Jp : Matrix (Fin dp) (Fin dp) ℝ)
    (Jm : Matrix (Fin dm) (Fin dm) ℝ)
    (R : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm) →
      EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm))
    (hsys : IsBlockSystem Jp Jm R) (𝒰 : Set (EuclideanSpace ℝ (Fin dp)))
    (G : EuclideanSpace ℝ (Fin dp) → EuclideanSpace ℝ (Fin dm))
    (hG : IsCenterStableGraph Jp Jm R 𝒰 G) :
    ∃ (Δ : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm) →
        Matrix (Fin dm) (Fin dm) ℝ) (C δ : ℝ), 0 < C ∧ 0 < δ ∧
      ∀ w : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm), ‖w‖ < δ →
        ‖matCLM (Δ w)‖ ≤ C * ‖w‖ ∧
          graphDefect Jp Jm R G w = matCLM (-Jm + Δ w) w.2 := by sorry

end ActiveSaddleSGD
