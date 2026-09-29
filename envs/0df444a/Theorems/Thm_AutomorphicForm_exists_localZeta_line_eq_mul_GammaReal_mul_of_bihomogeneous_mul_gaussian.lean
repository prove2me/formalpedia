-- Prove2me | Theorems.Thm_AutomorphicForm_exists_localZeta_line_eq_mul_GammaReal_mul_of_bihomogeneous_mul_gaussian
-- name    : AutomorphicForm.exists_localZeta_line_eq_mul_GammaReal_mul_of_bihomogeneous_mul_gaussian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/ecaf1951-7a37-5981-9e5a-eb8aa058c58a
-- title:
--   Archimedean zeta integral of bihomogeneous Gaussian as a Γ_ℝ-factor
-- statement:
--   Let $F$ be a field and $w$ an infinite place of $F$, with the completion $L = F_w$ carrying its Borel measurable structure, let $\mu_a$ be an additive Haar measure on $L$, and let $\chi\colon L^{\times}\to\mathbb C^{\times}$ be a group homomorphism such that $|\chi(u)| = 1$ for all $u$, such that $u\mapsto\chi(u)$ is continuous, and such that, for natural numbers $a,b$, one has $\chi(u)\,\iota_w(u)^{a}\,\overline{\iota_w(u)}^{\,b} = 1$ for every unit $u$ with $\|u\| = 1$, where $\iota_w =$ `Completion.extensionEmbedding w` is the canonical embedding $L\to\mathbb C$. Then there are real numbers $c > 0$ and $\tau$ such that for every function $P\colon L^{2}\to\mathbb C$ that is bihomogeneous of bidegree $(a,b)$, i.e. $P(t y) = \iota_w(t)^{a}\,\overline{\iota_w(t)}^{\,b}\,P(y)$ for all $t\in L$ and $y\in L^{2}$, every $z\in\mathbb C$ with $\operatorname{Re} z > 0$ and every $x\in L^{2}$ with $\sum_i \|x_i\|^{2} = 1$, the local zeta integral `localZeta` of the function $t\mapsto P(tx)\exp\bigl(-\pi\sum_i\|t x_i\|^{2}\bigr)$ against $\chi$ at $z$ equals $c\,\Gamma_{\mathbb R}\bigl(n_w z + (a+b) + \tau i\bigr)\,P(x)$, where $n_w$ is `w.mult`. Here `localZeta μa f χ z` is $\int f(x)\,\chi(x)\,|x|^{z}\,d^{\times}x$, with $\chi$ extended by $0$ at $0$, $|x|$ the module `modulus` of multiplication by $x$ (the `distribHaarChar` scaling factor, and $0$ at $x=0$), and $d^{\times}x$ the measure $\mu_a$ restricted to $L\smallsetminus\{0\}$ with density $|x|^{-1}$.
--
--   This is Tate's archimedean local computation: the zeta integral of a polynomial-type function times the Gaussian, restricted to the line through a unit vector, is a $\Gamma_{\mathbb R}$-factor times the value of the function, with a positive constant $c$ and a shift $\tau i$ absorbing the unnormalised Haar measure and the unramified part of $\chi$. It feeds the evaluation of Godement sections of polynomial-times-Gaussian data at the infinite places, used in [`AutomorphicForm.exists_sum_mul_localZeta_line_polynomial_mul_gaussian_eq_eval`](thm.html#AutomorphicForm.exists_sum_mul_localZeta_line_polynomial_mul_gaussian_eq_eval).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_localZeta_line_eq_mul_GammaReal_mul_of_bihomogeneous_mul_gaussian.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open LanglandsTunnell.TateLocal

theorem AutomorphicForm.exists_localZeta_line_eq_mul_GammaReal_mul_of_bihomogeneous_mul_gaussian
    (F : Type) [Field F] (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion]
    (μa : Measure w.Completion) [μa.IsAddHaarMeasure]
    (χ : (w.Completion)ˣ →* ℂˣ)
    (_hχ : ∀ u, ‖((χ u : ℂˣ) : ℂ)‖ = 1)
    (_hχc : Continuous fun u : (w.Completion)ˣ => ((χ u : ℂˣ) : ℂ))
    (a b : ℕ)
    (_hχab : ∀ u : (w.Completion)ˣ, ‖(u : w.Completion)‖ = 1 →
        ((χ u : ℂˣ) : ℂ) * (Completion.extensionEmbedding w (u : w.Completion) ^ a
          * starRingEnd ℂ (Completion.extensionEmbedding w (u : w.Completion)) ^ b) = 1) :
    ∃ (c τ : ℝ), 0 < c ∧
      ∀ (P : (Fin 2 → w.Completion) → ℂ),
        (∀ (t : w.Completion) (y : Fin 2 → w.Completion),
          P (fun i => t * y i)
            = Completion.extensionEmbedding w t ^ a
              * starRingEnd ℂ (Completion.extensionEmbedding w t) ^ b * P y) →
        ∀ z : ℂ, 0 < z.re →
          ∀ x : Fin 2 → w.Completion, ∑ i, ‖x i‖ ^ 2 = 1 →
            localZeta μa
                (fun t => P (fun i => t * x i)
                  * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖t * x i‖ ^ 2 : ℝ)) : ℂ)))
                χ z
              = (c : ℂ) * Complex.Gammaℝ ((w.mult : ℂ) * z + ((a + b : ℕ) : ℂ) + (τ : ℂ) * Complex.I)
                * P x := by sorry
