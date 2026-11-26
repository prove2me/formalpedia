-- Prove2me | Theorems.Thm_Arxiv2509_26304_trivial_invisible_structure
-- name    : Arxiv2509_26304.trivial_invisible_structure
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:07:07.490872+00:00
-- url     : https://prove2.me/theorems/9bfa9d40-8db3-5124-b231-3bf580b5b5a2
-- title:
--   Section 3: the trivial invisible structure (two horizontal walls) does not scatter the wave (10)
-- statement:
--   Let $\eta_0>0$ and $k>0$, and let the structure consist only of two infinitely thin horizontal PEC walls $\{(x,c_j):a_j\le x\le b_j\}$, $a_j<b_j$, $j=1,2$, at different heights $c_1\ne c_2$. Let $H^{\rm in}=e^{ikx}$ be the plane wave (10). Then:
--
--   1. $\nu\cdot\nabla H^{\rm in}=\partial_yH^{\rm in}=0$ on $\Gamma$;
--   2. $H^{\rm sc}=0$ solves the exterior Neumann problem (2)-(4) in $\Omega$, with far-field amplitude $F^{\rm sc}=0$;
--   3. the far-field amplitude of $H^{\rm sc}=0$ is $F^{\rm sc}(\theta)=0$ for every $\theta$;
--   4. the total scattering cross section is $\Sigma=0$.
--
--   So the structure is entirely invisible to (10).
--
--   **Formalization Note** The paper says (2)-(4) "has the trivial solution" $H^{\rm sc}=0$. The statement asserts that $0$ is a solution, and not that it is the only one: uniqueness of the exterior Neumann problem on open arcs is not stated in the paper and needs edge conditions at the wall tips that the paper does not give. The boundary condition (3) is imposed at the interior points of each wall, as limits from both sides. The walls may have different lengths. The hypothesis $c_1\ne c_2$ only records the paper's "two walls"; the conclusion holds without it, since $H^{\rm sc}=0$ satisfies every condition trivially. $\Sigma$ is the ratio (6), measured through any circle $|\boldsymbol\rho|=r$.
-- source:
--   Helsing and Karlsson, The uniqueness of inverse scattering problems, reciprocity principles, and nonradiating sources related to low-signature structures, arXiv:2509.26304v1 (2025), claim c001; Section 3, text after eq. (10), PDF p. 5; restated in Section 5, PDF p. 14

import Mathlib
import Definitions.Def_Arxiv2509_26304_Basic

open Filter Topology MeasureTheory

namespace Arxiv2509_26304

theorem trivial_invisible_structure (eta0 k : ℝ) (heta0 : 0 < eta0) (hk : 0 < k)
    (w₁ w₂ : HorizontalWall) (hw : w₁.c ≠ w₂.c) :
    (∀ p ∈ wallsGamma w₁ w₂, partialY (planeWaveH k 0) p = 0) ∧
    IsWallsNeumannSolution k w₁ w₂ (planeWaveH k 0) (fun _ => 0) (fun _ => 0) ∧
    (∀ F : ℝ → ℂ, HasFarFieldAmplitude k (fun _ => 0) F → ∀ θ : ℝ, F θ = 0) ∧
    (∀ r : ℝ, 0 < r → scatteringCrossSection eta0 k 0 (fun _ => 0) r = 0) := by sorry

end Arxiv2509_26304
