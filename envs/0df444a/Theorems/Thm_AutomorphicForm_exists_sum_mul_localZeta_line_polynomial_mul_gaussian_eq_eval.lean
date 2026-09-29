-- Prove2me | Theorems.Thm_AutomorphicForm_exists_sum_mul_localZeta_line_polynomial_mul_gaussian_eq_eval
-- name    : AutomorphicForm.exists_sum_mul_localZeta_line_polynomial_mul_gaussian_eq_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/1a87a09e-d9b2-5441-91b5-ac99bc234ba8
-- title:
--   Godement sections realising a polynomial on the unit sphere
-- statement:
--   Let $F$ be a field, $w$ an infinite place of $F$, and $L = F_w$ its completion, equipped with a measurable space structure compatible with the Borel structure; let $\mu_a$ be an additive Haar measure on $L$, and write $\iota_w =$ `Completion.extensionEmbedding w` for the canonical ring map $L \to \mathbb{C}$. Let $\chi : L^\times \to \mathbb{C}^\times$ be a group homomorphism whose values have absolute value $1$ and which is continuous as a $\mathbb{C}$-valued function, and let $P$ be a polynomial over $\mathbb{C}$ in the four variables indexed by $\mathrm{Fin}\,2 \oplus \mathrm{Fin}\,2$. For $y \in L^2$ write $P(y)$ for the value of $P$ at $(\iota_w(y_0), \iota_w(y_1); \overline{\iota_w(y_0)}, \overline{\iota_w(y_1)})$, the second block of variables receiving the complex conjugates. The assertion is that there exist $m \in \mathbb{N}$, functions $\Phi_j : L^2 \to \mathbb{C}$ and functions $e_j : \mathbb{C} \to \mathbb{C}$ for $j \in \mathrm{Fin}\,m$ such that: each $e_j$ is differentiable on all of $\mathbb{C}$; each $\Phi_j$ has the form $\Phi_j(y) = Q_j(y)\exp\!\big(-\pi \sum_i \|y_i\|^2\big)$ for some polynomial $Q_j$ in the same four variables, evaluated in the same way; and, for every $z$ with $\operatorname{Re} z > 0$ and every $x \in L^2$ with $\sum_i \|x_i\|^2 = 1$ satisfying $P(u x) = \chi(u)^{-1} P(x)$ for all units $u$ of $L$ with $\|u\| = 1$, one has $\sum_j e_j(z)\, Z(t \mapsto \Phi_j(t x), \chi, z) = P(x)$. Here $Z(f,\chi,z) = \int f(t)\,\chi^{\mathrm{ext}}(t)\,|t|^{z}\,d^\times t$ is the local zeta integral `localZeta`: $|t|$ denotes the module `modulus` of multiplication by $t$ (the value of the distributive Haar character on $t \neq 0$, and $0$ at $t = 0$), $\chi^{\mathrm{ext}}$ is $\chi$ extended by $0$ at $0$, and $d^\times t$ is $\mu_a$ restricted to $L \setminus \{0\}$ with density $|t|^{-1}$.
--
--   This is the archimedean analytic input to Jacquet–Langlands' Lemma 5.13 and its complex analogue: a polynomial in the bottom row of the maximal compact subgroup, transforming under the unit scalars by $\chi^{-1}$, is recovered on the unit sphere as a finite combination, with entire coefficients in the zeta variable, of Tate local zeta integrals of Gaussian-times-polynomial functions along the lines through the given vector. It feeds the construction of the Godement sections attached to a $K$-finite vector, being cited by [`AutomorphicForm.exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite`](thm.html#AutomorphicForm.exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_sum_mul_localZeta_line_polynomial_mul_gaussian_eq_eval.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open LanglandsTunnell.TateLocal

theorem AutomorphicForm.exists_sum_mul_localZeta_line_polynomial_mul_gaussian_eq_eval
    (F : Type) [Field F] (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion]
    (μa : Measure w.Completion) [μa.IsAddHaarMeasure]
    (χ : (w.Completion)ˣ →* ℂˣ)
    (_hχ : ∀ u, ‖((χ u : ℂˣ) : ℂ)‖ = 1)
    (_hχc : Continuous fun u : (w.Completion)ˣ => ((χ u : ℂˣ) : ℂ))
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) :
    ∃ (m : ℕ) (Φ : Fin m → (Fin 2 → w.Completion) → ℂ) (e : Fin m → ℂ → ℂ),
      (∀ j, Differentiable ℂ (e j)) ∧
      (∀ j, ∃ Q : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ, ∀ y : Fin 2 → w.Completion,
        Φ j y = MvPolynomial.eval
              (Sum.elim (fun i => Completion.extensionEmbedding w (y i))
                (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (y i)))) Q
            * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖y i‖ ^ 2 : ℝ)) : ℂ))) ∧
      ∀ z : ℂ, 0 < z.re →
        ∀ x : Fin 2 → w.Completion, ∑ i, ‖x i‖ ^ 2 = 1 →
          (∀ u : (w.Completion)ˣ, ‖(u : w.Completion)‖ = 1 →
            MvPolynomial.eval
                (Sum.elim (fun i => Completion.extensionEmbedding w ((u : w.Completion) * x i))
                  (fun i => starRingEnd ℂ (Completion.extensionEmbedding w ((u : w.Completion) * x i)))) P
              = ((χ u : ℂˣ) : ℂ)⁻¹ *
                MvPolynomial.eval
                  (Sum.elim (fun i => Completion.extensionEmbedding w (x i))
                    (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (x i)))) P) →
          (∑ j, e j z * localZeta μa (fun t => Φ j (fun i => t * x i)) χ z)
            = MvPolynomial.eval
                (Sum.elim (fun i => Completion.extensionEmbedding w (x i))
                  (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (x i)))) P := by sorry
