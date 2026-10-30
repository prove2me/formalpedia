-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_moving_frame_graph_angle_transport
-- name    : BirkhoffGlobalSection.moving_frame_graph_angle_transport
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:03:18.129515+00:00
-- url     : https://prove2.me/theorems/e6e2c84f-c048-4111-9b4f-dccd19c22021
-- title:
--   Graph-angle transport through a periodic symplectic frame
-- statement:
--   Let $F(t)\in\mathrm{Sp}(4,\mathbb R)$ be a continuous frame with $F(T)=F(0)$, where $T>0$. Suppose that its complex-linear determinant $d(F(t))$ satisfies $\operatorname{Re}(i\,d(F(t)))>0$. Let $\varphi:[0,1]\to SL(2,\mathbb R)$ be continuous with $\varphi(0)=I$. Define
--
--   $$Y(t)=F(0)^{-1}F(t)\operatorname{diag}(I_2,\varphi(t/T)).$$
--
--   There are a continuous determinant-angle lift $\theta$ of the graph unitary of $Y$ and a continuous polar-angle lift $\alpha$ of $\varphi$, both normalized to vanish at zero, with
--
--   $$\theta(T)=2\alpha(1).$$
--
--   This isolates the frame contribution in the HWZ index argument. It requires no globally homogeneous Hamiltonian: periodicity and the displayed half-plane condition suffice. The symplectic and complex-matrix algebra is reused from Mazecto's accepted homogeneous graph-angle transport proof; the result here exposes the general moving-frame statement.
-- source:
--   Derived generalization of Mazecto, accepted submission 893234ef-5ec2-4f4b-b415-f79ec1030002 for https://prove2.me/theorems/f880a9bf-1521-4b02-a828-1c90ceda0bb1. Context: Hofer-Wysocki-Zehnder, Ann. Math.148(1998), (3.35)-(3.39), https://doi.org/10.2307/120994. General hypotheses and conclusion checked directly against the reused proof; not asserted to be a verbatim numbered theorem.

import Definitions.Def_BirkhoffGlobalSection_MovingFrameAlgebra
open HryniewiczCriterion Matrix Complex

theorem BirkhoffGlobalSection.moving_frame_graph_angle_transport
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (T : ℝ) (hTpos : 0 < T)
    (hFsp : ∀ t, (F t).transpose * omegaMat * F t = omegaMat)
    (hFpos : ∀ t, 0 < (Complex.I * cdet (F t)).re)
    (hFc : ∀ i j, Continuous fun t => F t i j) (hFT : F T = F 0)
    (hφc : ∀ i j, ContinuousOn (fun t => φ t i j) (Set.Icc 0 1))
    (hφdet : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1) (hφ0 : φ 0 = 1) :
    ∃ θ α : ℝ → ℝ,
      IsDetAngleLift (fun t => graphUnitary4
        ((F 0)⁻¹ * F t * blockOne (φ (t / T)))) T θ ∧
      IsPolarAngleLift φ α ∧ θ T = 2 * α 1 := by sorry
