-- Prove2me | Theorems.Thm_Arxiv1504_01000_oa_two_maxima
-- name    : Arxiv1504_01000.oa_two_maxima
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T18:28:58.172473+00:00
-- url     : https://prove2.me/theorems/babd77a8-493f-4b99-94aa-a5ed9989ea5d
-- title:
--   Section III, eq. (9): two common maxima at $\phi$ and $\phi\pm\pi/4$
-- statement:
--   Let $[T]$ be a $3\times3$ Hermitian positive definite coherency matrix with $\Re T_{23}\neq0$, and let $L>0$. On $[-\pi/4,\pi/4]$ consider the two Hellinger distance curves
--
--   $$\theta\mapsto d_H(\sigma_3^2,\sigma_3^2(\theta)),\qquad \theta\mapsto d_H(\sigma_2^2,\sigma_2^2(\theta))$$
--
--   of eq. (9). Then:
--
--   1. both curves attain their maximum on $[-\pi/4,\pi/4]$, at $\phi_3$ and $\phi_2$;
--   2. there is a $\phi\in[-\pi/4,\pi/4]$ such that each of $\phi$, $\phi+\pi/4$ and $\phi-\pi/4$ is a local maximum of both curves;
--   3. every maximiser over $[-\pi/4,\pi/4]$ of either curve is one of $\phi$, $\phi+\pi/4$, $\phi-\pi/4$.
--
--   So the two curves share their peaks, and the peaks lie a quarter of a period, $\pi/4$, apart.
--
--   **Formalization Note** The hypothesis $\Re T_{23}\neq0$ is not in the paper. Without it the claim is false. If $\Re T_{23}=0$ and $T_{22}=T_{33}$, both curves vanish identically. If $\Re T_{23}=0$ and $T_{22}\neq T_{33}$, the angle $\theta=0$ is already an extremum of $T_{33}(\theta)$, and each curve has only one peak up to the period $\pi/2$.
-- source:
--   Bhattacharya, Muhuri, De, Manickam and Frery, Modifying the Yamaguchi Four-Component Decomposition Scattering Powers Using a Stochastic Distance, arXiv:1504.01000v1 (2015), claim c002 (a); Sec. III (Polarization Orientation Angle Estimation), eq. (9) and the paragraph after it, PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv1504_01000_Basic

open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace Arxiv1504_01000

theorem oa_two_maxima (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosDef) (L : ℝ) (hL : 0 < L)
    (hRe : (T 1 2).re ≠ 0) :
    (∃ φ₃ ∈ oaRange, IsMaxOn (dH T L 2) oaRange φ₃) ∧
    (∃ φ₂ ∈ oaRange, IsMaxOn (dH T L 1) oaRange φ₂) ∧
    ∃ φ ∈ oaRange,
      (∀ ψ ∈ ({φ, φ + Real.pi / 4, φ - Real.pi / 4} : Set ℝ),
        IsLocalMax (dH T L 2) ψ ∧ IsLocalMax (dH T L 1) ψ) ∧
      (∀ θ ∈ oaRange, (IsMaxOn (dH T L 2) oaRange θ ∨ IsMaxOn (dH T L 1) oaRange θ) →
        θ = φ ∨ θ = φ + Real.pi / 4 ∨ θ = φ - Real.pi / 4) := by sorry

end Arxiv1504_01000
