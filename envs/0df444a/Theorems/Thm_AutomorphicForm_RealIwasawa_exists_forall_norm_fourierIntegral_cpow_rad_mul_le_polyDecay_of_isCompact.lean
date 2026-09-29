-- Prove2me | Theorems.Thm_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact
-- name    : AutomorphicForm.RealIwasawa.exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/5f0bde91-85aa-50d1-84de-616baedd9f98
-- title:
--   Uniform polynomial decay of Fourier transforms of rad^{-u}P
-- statement:
--   Let $\mathcal G$ be a compact set of real $2\times 2$ matrices all of whose members have nonzero determinant, and let $U\subset\mathbb C$ be compact with $\operatorname{Re} u>1$ for every $u\in U$. Let $P$ assign to each real $2\times 2$ matrix a function $P\,g:\mathbb R\to\mathbb C$, such that $P\,g$ is $C^\infty$ for every $g\in\mathcal G$ and such that for each $n\in\mathbb N$ there is a constant $C>0$ with $\|\mathrm{D}^n(P\,g)(x)\|\le C$ (the norm of the $n$-th iterated Fréchet derivative) for all $g\in\mathcal G$ and all $x\in\mathbb R$. Let $L:\mathbb R\to\mathbb R\to\mathbb R$ be a continuous bilinear map and $c>0$ a real number such that for every $\xi\in\mathbb R$ there exists $v$ with $\|v\|\le 1$ and $c\|\xi\|\le\|L\,v\,\xi\|$, and let $N\in\mathbb N$. Then there is a single constant $C>0$ such that for all $g\in\mathcal G$, all $u\in U$ and all $\xi\in\mathbb R$, the Fourier integral with respect to Lebesgue measure, the standard additive character $\mathbf e(t)=e^{2\pi i t}$ and the pairing $L$, of the function
--   $$x\longmapsto \bigl(\sqrt{(g_{00}+x\,g_{10})^2+(g_{01}+x\,g_{11})^2}\bigr)^{-u}\,P\,g\,(x),$$
--   the complex power being taken of the nonnegative real square root, satisfies at $\xi$ the bound $C\,(1+\|\xi\|)^{-N}$.
--
--   This is the archimedean oscillatory-integral estimate underlying the real Iwasawa-coordinate analysis: rapid decay in the dual variable of the Fourier transform of a negative complex power of the quadratic radius $\mathrm{rad}(g,x)^2=(g_{00}+xg_{10})^2+(g_{01}+xg_{11})^2$ against a smooth amplitude, with a constant uniform in the matrix parameter $g$ and the exponent $u$ ranging over compacta and in the amplitude family. It is used to establish continuity and holomorphy together with polynomial decay for the weighted Fourier integrals of the associated automorphic expressions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean

import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Topology.Compactness.Compact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff FourierTransform

theorem AutomorphicForm.RealIwasawa.exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℝ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (hU : IsCompact U) (hU1 : ∀ u ∈ U, 1 < u.re)
    (P : Matrix (Fin 2) (Fin 2) ℝ → ℝ → ℂ) (hPC : ∀ g ∈ 𝒢, ContDiff ℝ ∞ (P g))
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ x : ℝ, ‖iteratedFDeriv ℝ n (P g) x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P g x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by sorry
