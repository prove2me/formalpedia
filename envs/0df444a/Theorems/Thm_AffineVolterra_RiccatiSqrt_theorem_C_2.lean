-- Prove2me | Theorems.Thm_AffineVolterra_RiccatiSqrt_theorem_C_2
-- name    : AffineVolterra.RiccatiSqrt.theorem_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:20.807268+00:00
-- url     : https://prove2.me/theorems/b35da9ad-c416-42b5-b682-3cba73976074
-- title:
--   Theorem C.2, p. 43 — invariance of the nonnegative orthant
-- statement:
--   Let $K$ be diagonal with scalar entries $K_i$ satisfying (2.5), and suppose every shift $\Delta_hK_i$, $h\in[0,1]$, satisfies (3.4). Let $u,v\in\mathbb R^d$ have nonnegative coordinates, let $F$ be locally integrable and nonnegative, and let $G$ be a locally square integrable real matrix function with nonnegative off-diagonal entries. Then
--   $$
--   \chi=Ku+v+K*(F+G\chi)
--   $$
--   has a unique locally square integrable solution, and every coordinate of that solution is nonnegative almost everywhere. This is the comparison principle used to keep the real part of the square-root Riccati solution nonpositive.
--
--   **Formalization Note** The signs of $F$ and $G$ are almost everywhere, appropriate for their $L^p$ classes. Every shifted kernel has its own resolvent measure. The diagonal entries of $G$ may have either sign.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Theorem C.2 and (C.2), p. 43

import Mathlib
import Definitions.Def_AffineVolterra_RiccatiSqrt_Setting

namespace AffineVolterra.RiccatiSqrt

open MeasureTheory

/-- Theorem C.2, p. 43: positivity for the diagonal linear equation. -/
theorem theorem_C_2 {d : ℕ} (Kd : Fin d → ℝ → ℝ)
    (u v : AffineVolterra.Transform.RVec d) (F : ℝ → AffineVolterra.Transform.RVec d) (G : ℝ → RMat d)
    (hK : ∀ i, ∃ γ : ℝ, Cond25 (Kd i) γ)
    (hshift : ∀ (i : Fin d) (h : ℝ), h ∈ Set.Icc 0 1 → Cond34 (shift h (Kd i)))
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hF : RealVecLpLoc 1 F)
    (hFpos : ∀ i, ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ F t i)
    (hG : RealMatLpLoc 2 G)
    (hGpos : ∀ i j, i ≠ j →
      ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ G t i j) :
    ∃ χ : ℝ → AffineVolterra.Transform.RVec d,
      RealVecLpLoc 2 χ ∧
      (∀ T : ℝ, 0 < T →
        SolvesOn (diagonalKernel Kd)
          (fun t i => ((Kd i t * u i + v i : ℝ) : ℂ))
          (fun t x => realVecToComplex (F t) +
            mulVec (realMatToComplex (G t)) x)
          (fun t => realVecToComplex (χ t)) T) ∧
      (∀ φ : ℝ → AffineVolterra.Transform.RVec d, RealVecLpLoc 2 φ →
        (∀ T : ℝ, 0 < T →
          SolvesOn (diagonalKernel Kd)
            (fun t i => ((Kd i t * u i + v i : ℝ) : ℂ))
            (fun t x => realVecToComplex (F t) +
              mulVec (realMatToComplex (G t)) x)
            (fun t => realVecToComplex (φ t)) T) →
        ∀ T : ℝ, 0 < T → φ =ᵐ[volume.restrict (Set.Ioc 0 T)] χ) ∧
      ∀ i, ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ χ t i := by sorry

end AffineVolterra.RiccatiSqrt
