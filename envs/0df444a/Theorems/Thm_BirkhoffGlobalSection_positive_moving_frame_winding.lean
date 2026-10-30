-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_positive_moving_frame_winding
-- name    : BirkhoffGlobalSection.positive_moving_frame_winding
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:06:46.221223+00:00
-- url     : https://prove2.me/theorems/aee38b11-9912-4366-ba12-0e94211d0568
-- title:
--   HWZ winding estimate in a positive periodic moving frame
-- statement:
--   Let $T>0$, let $F(t)$ be a continuous periodic symplectic frame with $F(T)=F(0)$ and $\operatorname{Re}(i\,d(F(t)))>0$, and let $\varphi:[0,1]\to SL(2,\mathbb R)$ be continuous with $\varphi(0)=I$. Suppose
--
--   $$Y(t)=F(0)^{-1}F(t)\operatorname{diag}(I_2,\varphi(t/T))$$
--
--   solves $\dot Y=JS(t)Y$ with a continuous symmetric positive definite generator $S(t)$. Every vector-angle lift of $\varphi$ then advances by more than one turn:
--
--   $$d>1\qquad\text{for every }d\in I(\varphi).$$
--
--   This is the analytic winding estimate needed for a local positive completion of a tangentially convex Hamiltonian. It assumes the displayed positive-system and frame data, without requiring a global homogeneous Hamiltonian or smoothness of $\varphi$ beyond continuity.
-- source:
--   Derived moving-frame version of the HWZ local index argument, Hofer-Wysocki-Zehnder, Ann. Math.148(1998), Theorem3.4, equations(3.33)-(3.46), https://doi.org/10.2307/120994. Uses the proved HryniewiczCriterion.positive_path_graph_angle_bound, https://prove2.me/theorems/fe83c257-af70-46a1-98bd-c14bbdedafd5, and the derived periodic-frame transport and regularity-free polar endpoint lemmas. Applies to the local-convexity frontier BirkhoffGlobalSection.dynamically_convex_on_strictly_convex_star_shaped_points.

import Definitions.Def_BirkhoffGlobalSection_MovingFrameAlgebra
open HryniewiczCriterion Matrix

theorem BirkhoffGlobalSection.positive_moving_frame_winding
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (T : ℝ) (hTpos : 0 < T)
    (hFsp : ∀ t, (F t).transpose * omegaMat * F t = omegaMat)
    (hFpos : ∀ t, 0 < (Complex.I * cdet (F t)).re)
    (hFc : ∀ i j, Continuous fun t => F t i j) (hFT : F T = F 0)
    (hφc : ∀ i j, ContinuousOn (fun t => φ t i j) (Set.Icc 0 1))
    (hφdet : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1) (hφ0 : φ 0 = 1)
    (S : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hSc : ∀ i j : Fin 4, Continuous fun t => S t i j)
    (hSpos : ∀ t, (S t).PosDef)
    (hd : ∀ t : ℝ, ∀ i j : Fin 4,
      HasDerivAt (fun s => ((F 0)⁻¹ * F s * blockOne (φ (s / T))) i j)
        ((symplJ4 * S t * ((F 0)⁻¹ * F t * blockOne (φ (t / T)))) i j) t) :
    ∀ d ∈ windingInterval φ, 1 < d := by sorry
