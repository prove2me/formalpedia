-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous
-- name    : AutomorphicForm.exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/6b3561b2-559e-5273-8f11-42528d9b99c0
-- title:
--   Continuous twisted sections at real scalars over ℂ/ℝ
-- statement:
--   Work with the quadratic extension $\mathbb{C}/\mathbb{R}$, the base algebra $A=\mathbb{R}$, and the twist given by complex conjugation $\sigma=$ `Complex.conjAe`, acting on $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ entrywise through `sigmaGL`. Fix a unit $d\in\mathbb{R}^\times$ and let $\delta=$ `toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)` be the image of the scalar matrix $d\cdot 1$ under the map induced by $\mathbb{R}\to\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}$, $a\mapsto 1\otimes a$. Let $\varphi:\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})\to\mathbb{C}$ be continuous with compact support, and let $\tau'$ be a measure on the twisted centraliser $T'=\{t: t\,\delta\,\sigma(t)^{-1}=\delta\}$, taken with the Borel $\sigma$-algebra of its subspace topology, which is assumed to be a Haar measure. The conclusion asserts the existence of a function $w:\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})\to\mathbb{R}$ which is a twisted section function for the data $(\delta,\tau',\varphi)$ — that is, $w\ge 0$ everywhere, $w$ is Borel measurable, $w$ has compact support, and for every $x$ with $\varphi(x^{-1}\delta\,\sigma(x))\neq 0$ one has $\int_{t\in T'} w(tx)\,d\tau'(t)=1$ — and which is moreover continuous.
--
--   This is the local archimedean (ramified-place) instance of the construction of a weight function used to unfold twisted orbital integrals: $w$ provides a normalisation along the $T'$-orbits meeting the support of $\varphi$, so that integration against $w$ converts integrals over $\mathrm{GL}_2$ into integrals over the twisted conjugacy class of $\delta$. It is used by [`AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime`](thm.html#AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime), where the twisted element is a scalar at a completion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous
    (d : ℝˣ) (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (τ' : @Measure
      (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ') :
    ∃ w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ,
      IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe
          (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) τ' φ w ∧
        Continuous w := by sorry
