-- Prove2me | Theorems.Thm_FiniteEnergyPlane_lt_of_mem_windingInterval_of_conj_of_loop
-- name    : FiniteEnergyPlane.lt_of_mem_windingInterval_of_conj_of_loop
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T14:00:42.995777+00:00
-- url     : https://prove2.me/theorems/080dd807-d632-4170-b369-20446357184a
-- title:
--   Winding thresholds pass through conjugation by a trivial loop, degenerate paths included
-- statement:
--   Let $G$ be a loop in $SL(2, \mathbb{R})$ on $[0, 1]$ (continuous, $\det G(t) = 1$, $G(1) = G(0)$) such that the path $t \mapsto G(t) G(0)^{-1} e_1$ has winding number zero, and let $\varphi$ be any path of $2 \times 2$ matrices. Let $k$ be an integer.
--
--   If every element of the winding interval of $t \mapsto G(t) \varphi(t) G(0)^{-1}$ is greater than $k$, then every element of the winding interval of $\varphi$ is greater than $k$.
--
--   **Role.** Winding thresholds, and hence lower bounds on the Conley–Zehnder index, do not depend on the choice of a homotopically trivial frame. No condition on $\varphi(1)$ is imposed, so the statement covers degenerate paths, where the earlier frame-change invariance `czIndexOfPath_conj_of_loop` does not apply.
--
--   **Formalization Note.** The winding number zero hypothesis is the angle function $\theta$ with $\theta(1) = \theta(0)$ and $G(t) G(0)^{-1} e_1 = r\, e^{i\theta(t)}$, $r > 0$. The winding interval is `HryniewiczCriterion.windingInterval`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.1.1 (winding interval and the index on degenerate paths)

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open HryniewiczCriterion

namespace FiniteEnergyPlane

/-- Let `G` be a loop in `SL(2, ℝ)` such that `t ↦ G(t) G(0)⁻¹ e₁` has winding number zero, and let
`φ` be any path. If every element of the winding interval of `t ↦ G(t) φ(t) G(0)⁻¹` is greater than
the integer `k`, then every element of the winding interval of `φ` is greater than `k`. No condition
on `φ(1)` is imposed, so degenerate paths are allowed. -/
theorem lt_of_mem_windingInterval_of_conj_of_loop (φ G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ContinuousOn G (Set.Icc 0 1)) (hGd : ∀ t ∈ Set.Icc (0 : ℝ) 1, (G t).det = 1)
    (hG1 : G 1 = G 0) (θ : ℝ → ℝ) (hθc : ContinuousOn θ (Set.Icc 0 1)) (hθ1 : θ 1 = θ 0)
    (hθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧
      (G t * (G 0)⁻¹).mulVec (rotationVector 0) = r • rotationVector (θ t)) (k : ℤ)
    (h : ∀ d ∈ windingInterval (fun t => G t * φ t * (G 0)⁻¹), (k : ℝ) < d) :
    ∀ d ∈ windingInterval φ, (k : ℝ) < d := by
  sorry

end FiniteEnergyPlane
