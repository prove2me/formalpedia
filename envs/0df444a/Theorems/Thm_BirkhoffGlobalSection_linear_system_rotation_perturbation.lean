-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_linear_system_rotation_perturbation
-- name    : BirkhoffGlobalSection.linear_system_rotation_perturbation
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T17:49:47.141756+00:00
-- url     : https://prove2.me/theorems/6f856044-c95c-4753-b784-e4c41816d145
-- title:
--   Robustness of ambient rotation under coefficient perturbation
-- statement:
--   Ambient rotation increments depend continuously on the coefficients of a linear Hamiltonian system.
--
--   Let $K$ be a real symmetric $4\times4$ matrix and let $L>0$. There is $\delta>0$ with the following property. Let $a\in\mathbb R$, and let $H$ be continuous and symmetric on $[a,a+L]$ with $\|H(t)-K\|_{\max}<\delta$. Let $\Phi$ and $\Phi_0$ solve
--
--   $$
--   \Phi'=JH\,\Phi,\qquad \Phi_0'=JK\,\Phi_0,\qquad \Phi(a)=\Phi_0(a)=\mathrm{id}
--   $$
--
--   on $[a,a+L]$, and let $\alpha,\alpha_0$ be continuous arguments on $[a,a+L]$ of the ambient determinants $d(\Phi(t))$ and $d(\Phi_0(t))$. Then
--
--   $$
--   \alpha(a+L)-\alpha(a)>\alpha_0(a+L)-\alpha_0(a)-\pi .
--   $$
--
--   The constant $\delta$ depends only on $K$ and $L$, not on $a$. This is the finite-time robustness used when the coefficients along a trajectory stay close to their value at an equilibrium.
--
--   **Formalization Note** The norm is the entrywise maximum norm (`Matrix.Norms.Elementwise`). All hypotheses are imposed only on the closed interval.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S7, proof of Theorem 1.8 (the Hessian along the orbit is taken arbitrarily close to its value at the saddle-center over the resident time interval). Continuous dependence of linear ODE solutions on coefficients (Gronwall inequality); Gutt, Generalized Conley--Zehnder index, https://arxiv.org/pdf/1307.7239, Eq. (9).

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation
import Mathlib.Analysis.Matrix.Normed
open scoped Matrix.Norms.Elementwise

namespace BirkhoffGlobalSection

/-- Robustness of ambient rotation under small changes of the coefficients.
For a symmetric constant matrix `K` and a length `L > 0` there is `δ > 0` such
that, on any interval `[a, a + L]`, the fundamental solutions of `Φ' = J H Φ`
and `Φ₀' = J K Φ₀` (both equal to the identity at `a`) have continuous ambient
angles whose increments differ by less than `π`, whenever `H` is continuous,
symmetric and `δ`-close to `K` in the entrywise norm. -/
theorem linear_system_rotation_perturbation (K : Matrix (Fin 4) (Fin 4) ℝ)
    (hK : ∀ i j : Fin 4, K i j = K j i) (L : ℝ) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : ℝ) (H : ℝ → Matrix (Fin 4) (Fin 4) ℝ),
        ContinuousOn H (Set.Icc a (a + L)) →
        (∀ t ∈ Set.Icc a (a + L), ∀ i j : Fin 4, H t i j = H t j i) →
        (∀ t ∈ Set.Icc a (a + L), ‖H t - K‖ < δ) →
        ∀ Φ Φ₀ : ℝ → (Phase →L[ℝ] Phase),
          Φ a = ContinuousLinearMap.id ℝ Phase →
          Φ₀ a = ContinuousLinearMap.id ℝ Phase →
          (∀ t ∈ Set.Icc a (a + L), ∀ v : Phase,
            HasDerivAt (fun τ => Φ τ v)
              (TangentialHessian.qI.mulVec ((H t).mulVec (Φ t v))) t) →
          (∀ t ∈ Set.Icc a (a + L), ∀ v : Phase,
            HasDerivAt (fun τ => Φ₀ τ v) (TangentialHessian.qI.mulVec (K.mulVec (Φ₀ t v))) t) →
          ∀ α α₀ : ℝ → ℝ,
            ContinuousOn α (Set.Icc a (a + L)) → ContinuousOn α₀ (Set.Icc a (a + L)) →
            (∀ t ∈ Set.Icc a (a + L), ∃ ρ : ℝ, 0 < ρ ∧
              ambientRotationDet (Φ t) = ⟨ρ * Real.cos (α t), ρ * Real.sin (α t)⟩) →
            (∀ t ∈ Set.Icc a (a + L), ∃ ρ : ℝ, 0 < ρ ∧
              ambientRotationDet (Φ₀ t) = ⟨ρ * Real.cos (α₀ t), ρ * Real.sin (α₀ t)⟩) →
            α₀ (a + L) - α₀ a - Real.pi < α (a + L) - α a := by sorry

end BirkhoffGlobalSection
