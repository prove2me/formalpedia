-- Prove2me | Theorems.Thm_BlockBochner_lemma_20
-- name    : BlockBochner.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:09.365871+00:00
-- url     : https://prove2.me/theorems/2d70c2ac-82bd-487e-bbd3-48ecea8c2a91
-- title:
--   Lemma 20 — Bochner operator lemma
-- statement:
--   Let $H_0,H_1,H_2$ be real Hilbert spaces and $d_0:H_0\to H_1$, $d_1:H_1\to H_2$ bounded linear maps with $d_1d_0=0$. Define $Q=d_0^*d_0$ and $B=d_0d_0^*+d_1^*d_1$. If $B\succeq\alpha I$ for some $\alpha>0$, then $B$ is boundedly invertible and
--   $$Q^2=d_0^*Bd_0\succeq\alpha Q\qquad\text{and}\qquad P=d_0^*B^{-1}d_0\preceq\alpha^{-1}Q,$$
--   where $P$ is the orthogonal projection onto $(\ker d_0)^\perp$.
--
--   Applied to $d_0f=(P_if)_i$ and $d_1(f_i)=(P_{ij}(f_i-f_j))_{i<j}$ it gives the Bochner and Poincaré inequalities.
--
--   Differences from the source: none.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Lemma 20, p.21

import Mathlib

namespace BlockBochner

/-- **Lemma 20 (Bochner operator lemma).** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Lemma 20, p.21. Let `H₀, H₁, H₂` be Hilbert spaces and
`d₀ : H₀ → H₁`, `d₁ : H₁ → H₂` bounded linear maps with `d₁ d₀ = 0`; `Q = d₀* d₀`,
`B = d₀ d₀* + d₁* d₁`. If `B ⪰ αI` for some `α > 0`, then `B` is boundedly invertible,
`Q² = d₀* B d₀ ⪰ αQ`, and `P = d₀* B⁻¹ d₀ ⪯ α⁻¹ Q`, where `P` is the orthogonal projection onto
`(ker d₀)^⊥`.

**Formalization Note** Real Hilbert spaces; `B⁻¹` is `Ring.inverse B`; `⪯` is the order of quadratic
forms. -/
theorem lemma_20 {H₀ H₁ H₂ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
    (d₀ : H₀ →L[ℝ] H₁) (d₁ : H₁ →L[ℝ] H₂) (hd : d₁ ∘L d₀ = 0) {α : ℝ} (hα : 0 < α)
    (hB : ∀ x, α * ‖x‖ ^ 2 ≤
      inner ℝ x ((d₀ ∘L ContinuousLinearMap.adjoint d₀ + ContinuousLinearMap.adjoint d₁ ∘L d₁) x)) :
    let Q := ContinuousLinearMap.adjoint d₀ ∘L d₀
    let B := d₀ ∘L ContinuousLinearMap.adjoint d₀ + ContinuousLinearMap.adjoint d₁ ∘L d₁
    IsUnit B ∧ Q ∘L Q = ContinuousLinearMap.adjoint d₀ ∘L B ∘L d₀ ∧
      (∀ x, α * inner ℝ x (Q x) ≤ inner ℝ x ((Q ∘L Q) x)) ∧
      (LinearMap.ker d₀.toLinearMap)ᗮ.starProjection =
        ContinuousLinearMap.adjoint d₀ ∘L Ring.inverse B ∘L d₀ ∧
      ∀ x, inner ℝ x ((LinearMap.ker d₀.toLinearMap)ᗮ.starProjection x) ≤
        α⁻¹ * inner ℝ x (Q x) := by sorry

end BlockBochner
