-- Prove2me | Theorems.Thm_AffineVolterra_RiccatiSqrt_lemma_6_3
-- name    : AffineVolterra.RiccatiSqrt.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:19.054436+00:00
-- url     : https://prove2.me/theorems/531d3850-13e9-4bdb-becb-708c1f2e9fb3
-- title:
--   Lemma 6.3, p. 29 — global square-root Riccati–Volterra solution
-- statement:
--   Let $K$ be diagonal with entries $K_i$ satisfying (2.5), and suppose $\Delta_hK_i$ satisfies (3.4) for every $h\in[0,1]$. Fix $\sigma_i>0$ and a real matrix $B$ with $B_{ij}\ge0$ for $i\ne j$. For a complex row vector $u$ and locally integrable complex row function $f$ with $\operatorname{Re}u_i\le0$ and $\operatorname{Re}f_i\le0$, the square-root Riccati–Volterra equation
--   $$
--   \psi_i(t)=u_iK_i(t)+\int_0^t K_i(t-s)\left(f_i(s)+\sum_j\psi_j(s)B_{ji}+\frac{\sigma_i^2}{2}\psi_i(s)^2\right)\,ds
--   $$
--   has a unique global solution $\psi\in L^2_{\mathrm{loc}}(\mathbb R_+,\mathbb C^d)$, and $\operatorname{Re}\psi_i\le0$ almost everywhere for every $i$. This is the deterministic transform-equation result used in Theorem 6.1(ii).
--
--   **Formalization Note** Signs of $L^1$ functions and the conclusion for an $L^2$ solution are interpreted almost everywhere. The condition $b^0\in\mathbb R_+^d$ from (6.1) is absent because $b^0$ does not enter (6.3). The coupling is by the $i$-th column of $B$, and the convolution integral is required to be integrable wherever the equation is asserted.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Lemma 6.3, p. 29; (6.3), p. 27; Theorem 6.1, p. 28

import Mathlib
import Definitions.Def_AffineVolterra_RiccatiSqrt_Setting

namespace AffineVolterra.RiccatiSqrt

open MeasureTheory

/-- Lemma 6.3, p. 29: the first sentence of Theorem 6.1(ii). -/
theorem lemma_6_3 {d : ℕ} (Kd : Fin d → ℝ → ℝ)
    (B : RMat d) (σ : AffineVolterra.Transform.RVec d) (u : AffineVolterra.Transform.CVec d) (f : ℝ → AffineVolterra.Transform.CVec d)
    (hK : ∀ i, ∃ γ : ℝ, Cond25 (Kd i) γ)
    (hshift : ∀ (i : Fin d) (h : ℝ), h ∈ Set.Icc 0 1 → Cond34 (shift h (Kd i)))
    (hσ : ∀ i, 0 < σ i)
    (hB : ∀ i j, i ≠ j → 0 ≤ B i j)
    (hu : ∀ i, (u i).re ≤ 0)
    (hf : VecLpLoc 1 f)
    (hfneg : ∀ i, ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), (f t i).re ≤ 0) :
    ∃ ψ : ℝ → AffineVolterra.Transform.CVec d,
      IsGlobal (diagonalKernel Kd) (squareRootSource Kd u)
        (squareRootDrift B σ f) ψ ∧
      (∀ i, ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), (ψ t i).re ≤ 0) ∧
      ∀ φ : ℝ → AffineVolterra.Transform.CVec d,
        IsGlobal (diagonalKernel Kd) (squareRootSource Kd u)
          (squareRootDrift B σ f) φ →
        ∀ T : ℝ, 0 < T → φ =ᵐ[volume.restrict (Set.Ioc 0 T)] ψ := by sorry

end AffineVolterra.RiccatiSqrt
