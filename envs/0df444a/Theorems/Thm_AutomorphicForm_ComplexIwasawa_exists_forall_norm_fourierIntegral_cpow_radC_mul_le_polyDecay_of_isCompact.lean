-- Prove2me | Theorems.Thm_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact
-- name    : AutomorphicForm.ComplexIwasawa.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/e746be1f-6ccf-56d2-91c4-8afb756deb7e
-- title:
--   Uniform rapid decay of Fourier integrals of radC^{-u}P
-- statement:
--   For a complex $2\times 2$ matrix $g$ put $\operatorname{radC}(g,z)=\sqrt{|g_{00}+z\,g_{10}|^{2}+|g_{01}+z\,g_{11}|^{2}}$ (the square root of the sum of the squared moduli of $\mathrm{botP}(g,z)=g_{00}+z\,g_{10}$ and $\mathrm{botQ}(g,z)=g_{01}+z\,g_{11}$). Let $\mathcal G$ be a compact set of complex $2\times2$ matrices all of whose members have nonzero determinant, let $U\subseteq\mathbb C$ be compact with $\operatorname{Re}u>2$ for every $u\in U$, and let $P$ assign to each matrix $g$ a function $P(g,\cdot)\colon\mathbb C\to\mathbb C$ such that $P(g,\cdot)$ is $C^{\infty}$ as a function of the two real variables for every $g\in\mathcal G$, and such that for every $n$ there is $C_n>0$ bounding $\|D^{n}P(g,z)\|$ for all $g\in\mathcal G$ and all $z\in\mathbb C$ (iterated Fréchet derivatives over $\mathbb R$). Let $L\colon\mathbb C\times\mathbb C\to\mathbb R$ be a continuous $\mathbb R$-bilinear form and $c>0$ be such that for every $\xi$ there is $v$ with $\|v\|\le 1$ and $c\|\xi\|\le\|L(v,\xi)\|$. Then for every $N\in\mathbb N$ there exists $C>0$ with
--   $$\Bigl\|\int_{\mathbb C}\mathbf e(-L(z,\xi))\,\operatorname{radC}(g,z)^{-u}P(g,z)\,dz\Bigr\|\le C\,(1+\|\xi\|)^{-N}$$
--   for all $g\in\mathcal G$, $u\in U$ and $\xi\in\mathbb C$, the integral being the vector-valued Fourier integral with respect to Lebesgue measure on $\mathbb C$ and the pairing $L$.
--
--   This is the uniform (in the matrix parameter $g$, the exponent $u$ and the family $P$) form of the statement that the Fourier transform of $\operatorname{radC}(g,\cdot)^{-u}P(g,\cdot)$ decays faster than any power, the analytic input at a complex place to the moderate growth of $\mathrm{GL}_2$ Eisenstein series uniformly in the spectral parameter. It is used in the proof of [`AutomorphicForm.ComplexIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral`](thm.html#AutomorphicForm.ComplexIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral), and rests on uniform bounds for the iterated derivatives of $z\mapsto \operatorname{radC}(g,z)^{-u}$ together with the uniform integrability of $\operatorname{radC}(g,\cdot)^{-\kappa}$ for $\kappa>2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact.lean

import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Topology.Compactness.Compact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm.ComplexIwasawa
open scoped ContDiff FourierTransform

theorem AutomorphicForm.ComplexIwasawa.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (hU : IsCompact U) (hU2 : ∀ u ∈ U, 2 < u.re)
    (P : Matrix (Fin 2) (Fin 2) ℂ → ℂ → ℂ) (hPC : ∀ g ∈ 𝒢, ContDiff ℝ ∞ (P g))
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ z : ℂ, ‖iteratedFDeriv ℝ n (P g) z‖ ≤ C)
    (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℂ, ∃ v : ℂ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ ξ : ℂ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun z => ((radC g z : ℂ) ^ (-u)) * P g z) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by sorry
