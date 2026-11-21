-- Prove2me | Theorems.Thm_Euler_exists_compact_smooth_euler_singularity
-- name    : Euler.exists_compact_smooth_euler_singularity
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T13:42:22.508142+00:00
-- url     : https://prove2.me/theorems/fe9fbdb2-5c5f-4674-9192-2447d5bdf861
-- title:
--   Finite-time Euler singularity from smooth compact data (Theorem 1.1, quantitative form)
-- statement:
--   This is the quantitative form of Theorem 1.1 of the OpenAI paper *Finite time blowup for the Euler equation*: a smooth, compactly supported, divergence-free initial velocity on $\mathbb{R}^3$ whose unforced Euler solution develops a singularity in finite time.
--
--   There exist an initial velocity $u_0$, a time $T_*\in(0,1]$, and fields $v,p$ such that:
--
--   1. $u_0$ is smooth, divergence-free, rapidly decaying, **compactly supported**, and **nonzero**;
--   2. $(v,p)$ solves unforced Euler on the half-open interval $[0,T_*)$ in the all-order Sobolev class (the velocity and its strong time derivative have continuous $L^2$ spatial jets of every order), with uniformly bounded kinetic energy;
--   3. for every $T>0$, a closed-interval solution in this class on $[0,T]$ exists **if and only if** $T<T_*$ (maximal lifespan);
--   4. on every shorter closed interval $[0,T]\subset[0,T_*)$ the $C^1$ norm of $v$ and the time integral of the vorticity norm are finite;
--   5. at the endpoint,
--   $$\limsup_{t\uparrow T_*}\|v(t)\|_{C^1}=\infty,\qquad \int_0^{T_*}\|\operatorname{curl}v(t)\|_{L^\infty}\,dt=\infty;$$
--   6. the same datum admits no global smooth finite-energy Euler solution on $\mathbb{R}^3\times[0,\infty)$.
--
--   The $C^1$ norm is the sum of the spatial suprema of $\|v\|$ and $\|\nabla v\|$; the vorticity norm is the spatial supremum of $\|\operatorname{curl}v\|$. Both are taken in $\mathbb{R}_{\ge0}\cup\{\infty\}$, so the blowup assertions are equalities with $\infty$. The bound $T_*\le1$ is a normalization. This theorem implies the global-breakdown form `Euler.euler_breakdown_R3`.
--
--   **Formalization Note.** The statement is the independent Comparator reference theorem `exists_compact_smooth_euler_singularity`, proved in the repository's `Euler/Solution.lean`; suprema and the vorticity integral are `ℝ≥0∞`-valued (`⊤` denotes infinity). Axioms: `propext`, `Classical.choice`, `Quot.sound`.
-- source:
--   OpenAI, Finite time blowup for the Euler equation (2026), https://cdn.openai.com/pdf/315b36cd-ec98-4023-8342-93345194ece1/euler.pdf, Theorem 1.1; Lean reference: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/Euler.lean#L164-L184; proved in https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/Euler/Solution.lean#L40-L75.

import Mathlib
import Definitions.Def_EulerComparatorChallenge

open ContDiff Set InnerProductSpace MeasureTheory
open scoped ENNReal Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Euler
theorem exists_compact_smooth_euler_singularity :
    ∃ (u₀ : ℝ³ → ℝ³) (Tstar : ℝ) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      InitialVelocityConditionDecay u₀ ∧ HasCompactSupport u₀ ∧ u₀ ≠ 0 ∧
      0 < Tstar ∧ Tstar ≤ 1 ∧
      EulerSobolevExistenceAndSmoothnessR3On (Ico 0 Tstar) u₀ v p ∧
      (∃ E : ℝ, ∀ t ∈ Ico (0 : ℝ) Tstar, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E) ∧
      (∀ T : ℝ, 0 < T →
        ((∃ w q, EulerSobolevExistenceAndSmoothnessR3On (Icc 0 T) u₀ w q) ↔ T < Tstar)) ∧
      (∀ T ∈ Ioo 0 Tstar,
        (⨆ t ∈ Icc (0 : ℝ) T, velocityC1Norm (v · t)) < ⊤ ∧
        (∫⁻ t in Ico (0 : ℝ) T, vorticityNorm (v · t)) < ⊤) ∧
      Filter.limsup (fun t : ℝ => velocityC1Norm (v · t)) (𝓝[<] Tstar) = ⊤ ∧
      (∫⁻ t in Ico (0 : ℝ) Tstar, vorticityNorm (v · t)) = ⊤ ∧
      ¬ (∃ w q, EulerExistenceAndSmoothnessR3 u₀ w q) := by
  sorry
end Euler
