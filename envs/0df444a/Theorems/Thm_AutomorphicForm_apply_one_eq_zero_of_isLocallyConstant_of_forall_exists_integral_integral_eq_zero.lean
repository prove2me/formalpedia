-- Prove2me | Theorems.Thm_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero
-- name    : AutomorphicForm.apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/7b5d257f-eadd-5bcc-abfe-f218ed303895
-- title:
--   Vanishing at 1 from shrinking elliptic orbital integrals
-- statement:
--   Let $F$ be a nontrivially normed field whose norm is ultrametric and which is a proper metric space (so closed balls are compact), equipped with Borel measurable structures on $F$ and on $F^\times$; let $\mu$ be an additive Haar measure on $F$ and $\nu$ a Haar measure on the multiplicative group $F^\times$. Let $\Phi : \mathrm{M}_2(F) \to \mathbb{C}$ be locally constant with compact support, and let $\varpi \in F$ satisfy $\|\varpi\| < 1$ together with $\|a\|^2 \neq \|\varpi\| \cdot \|t\|^2$ for all $a \in F$ and all $t \neq 0$. Assume that for every real $\varepsilon > 0$ there are $r, r' \in F$ with $r' \neq 0$ and $\|r'\| < \|r\| < \varepsilon$ (so $r \neq 0$ as well) for which both iterated integrals $$\int_{F^\times} \int_F \Phi\left(1 + \begin{pmatrix} a & b \\ (\varpi \lambda^2 - a^2)/b & -a \end{pmatrix}\right) \, d\mu(a) \, d\nu(b)$$ vanish, for $\lambda = r$ and for $\lambda = r'$, where $1$ is the identity matrix and $b \in F^\times$ is viewed in $F$. The conclusion is that $\Phi(1) = 0$.
--
--   The matrices $1 + Y$ with $Y$ of trace $0$ and determinant $-\varpi\lambda^2$ sweep out the conjugacy class of a regular element of a ramified elliptic torus of $\mathrm{GL}_2(F)$, and in the coordinates $(a,b)$ the displayed iterated integral is the corresponding orbital integral of $\Phi$ up to a positive factor; the statement thus says that a locally constant compactly supported $\Phi$ with ramified elliptic orbital integrals vanishing along classes shrinking to $1$ must vanish at $1$, in the spirit of the local vanishing and germ results of Shalika and Langlands. It is used in the proof of [`AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegral_eq_zero`](thm.html#AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegral_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero
    {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    (μ : Measure F) [μ.IsAddHaarMeasure] (ν : Measure Fˣ) [ν.IsHaarMeasure]
    (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (ϖ : F) (hϖ : ‖ϖ‖ < 1) (hϖsq : ∀ a t : F, t ≠ 0 → ‖a‖ ^ 2 ≠ ‖ϖ‖ * ‖t‖ ^ 2)
    (hvan : ∀ ε : ℝ, 0 < ε → ∃ r r' : F, r' ≠ 0 ∧ ‖r'‖ < ‖r‖ ∧ ‖r‖ < ε ∧
      (∫ b, ∫ a, Φ (1 + !![a, (b : F); (ϖ * r ^ 2 - a ^ 2) / b, -a]) ∂μ ∂ν) = 0 ∧
      (∫ b, ∫ a, Φ (1 + !![a, (b : F); (ϖ * r' ^ 2 - a ^ 2) / b, -a]) ∂μ ∂ν) = 0) :
    Φ 1 = 0 := by sorry
