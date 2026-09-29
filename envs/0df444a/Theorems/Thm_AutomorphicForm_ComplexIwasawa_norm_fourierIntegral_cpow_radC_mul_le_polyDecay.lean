-- Prove2me | Theorems.Thm_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay
-- name    : AutomorphicForm.ComplexIwasawa.norm_fourierIntegral_cpow_radC_mul_le_polyDecay
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/910042b7-6a03-5815-81b7-0ae88b8cee4e
-- title:
--   Polynomial decay of the Fourier transform of (radC g)^{-u}P
-- statement:
--   Let $g$ be a $2\times 2$ complex matrix with $\det g \neq 0$, and let $u \in \mathbb{C}$ satisfy $\operatorname{Re} u > 2$. Let $P : \mathbb{C} \to \mathbb{C}$ be $C^\infty$ as a function on $\mathbb{C}$ regarded as a real vector space, with each iterated Fréchet derivative $D^n P$ bounded on $\mathbb{C}$ by some constant $C_n > 0$ (a bound for each order $n$, uniform in the point). Let $L : \mathbb{C} \to \mathbb{C} \to \mathbb{R}$ be a continuous $\mathbb{R}$-bilinear form which is coercive in its second argument with constant $c > 0$: for every $\xi \in \mathbb{C}$ there is $v$ with $\|v\| \le 1$ and $c\|\xi\| \le |L(v,\xi)|$. Finally let $N$ be a natural number. Then there is a constant $C > 0$ such that for all $\xi \in \mathbb{C}$ the vector-valued Fourier integral of $z \mapsto (\mathrm{radC}\,g\,z)^{-u} P(z)$ with respect to Lebesgue measure on $\mathbb{C}$, the standard additive character $\mathbf{e}(t) = e^{2\pi i t}$ and the pairing $L$, has norm at most $C(1+\|\xi\|)^{-N}$. Here $\mathrm{radC}\,g\,z = \sqrt{|g_{00} + z g_{10}|^2 + |g_{01} + z g_{11}|^2}$, and the complex power $(\mathrm{radC}\,g\,z)^{-u}$ is taken of its coercion to $\mathbb{C}$.
--
--   This isolates the archimedean estimate at a complex place needed for the rapid decay of Whittaker-type coefficients for $\mathrm{GL}_2$: the Fourier transform, in the unipotent variable, of an Eisenstein-type integrand $(\mathrm{radC}\,g)^{-u}$ twisted by a smooth function with bounded derivatives decays faster than any fixed polynomial rate. It is used in the proof of the polynomial decay of the corresponding unipotent integral against an additive character for unitary $g$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean

import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory AutomorphicForm.ComplexIwasawa
open scoped ContDiff FourierTransform

theorem AutomorphicForm.ComplexIwasawa.norm_fourierIntegral_cpow_radC_mul_le_polyDecay
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) {u : ℂ} (hu : 2 < u.re)
    {P : ℂ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖iteratedFDeriv ℝ n P z‖ ≤ C)
    (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℂ, ∃ v : ℂ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℂ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun z => ((radC g z : ℂ) ^ (-u)) * P z) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by sorry
