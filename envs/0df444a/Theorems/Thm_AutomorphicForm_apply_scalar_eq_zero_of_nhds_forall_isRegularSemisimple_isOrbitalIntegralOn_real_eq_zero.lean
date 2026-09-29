-- Prove2me | Theorems.Thm_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero
-- name    : AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/41139c90-e1c7-5cd8-9c0f-89413190977e
-- title:
--   Harish-Chandra limit formula on GL₂(ℝ): vanishing form
-- statement:
--   Let $\mu$ be a Haar measure on $G=\mathrm{GL}_2(\mathbb{R})$ for the Borel $\sigma$-algebra of its topology, let $f\colon G\to\mathbb{C}$ be a function that is compactly supported and arises from a $C^\infty$ function $\Phi$ of the four matrix entries, so that $f(g)=\Phi\big((g_{ij})\big)$ for all $g$, and let $c\in\mathbb{R}^\times$. Assume there is a neighbourhood $U$ of the scalar matrix $c\cdot 1$ in $G$ with the following property: for every $\gamma\in U$ whose determinant, as a unit of $\mathbb{R}$, equals $c^2$ and which is regular semisimple in the sense that $\mathrm{tr}(\gamma)^2-4\det(\gamma)$ is a unit of $\mathbb{R}$, for every Haar measure $\tau$ on the centraliser of $\{\gamma\}$ in $G$ (with its Borel structure), and for every $I\in\mathbb{C}$ for which the orbital-integral relation holds at $\gamma$ relative to $(\mu,\tau)$ — that is, there is $w\colon G\to\mathbb{R}$ nonnegative, measurable and compactly supported with $\int_{Z(\gamma)}w(tx)\,d\tau(t)=1$ for every $x$ with $f(x^{-1}\gamma x)\neq 0$, and $I=\int_G f(x^{-1}\gamma x)\,w(x)\,d\mu(x)$ — one has $I=0$. The conclusion is $f(c\cdot 1)=0$.
--
--   This is the vanishing form of Harish-Chandra's limit formula at a central element of $\mathrm{GL}_2(\mathbb{R})$: regular semisimple orbital integrals vanishing throughout a neighbourhood of a scalar force the test function to vanish at that scalar. It is the real-place input to the archimedean step of the trace-formula comparison for cyclic base change, and is used by the results identifying orbital integrals at scalars with twisted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero
    (μ : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μ)
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ Φ : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, f g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (c : ℝˣ)
    (hvan : ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = c ^ 2 → IsRegularSemisimple γ →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ γ τ f I → I = 0) :
    f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0 := by sorry
