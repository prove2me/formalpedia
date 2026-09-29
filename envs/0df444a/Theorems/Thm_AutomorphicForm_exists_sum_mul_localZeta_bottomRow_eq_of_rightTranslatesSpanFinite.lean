-- Prove2me | Theorems.Thm_AutomorphicForm_exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite
-- name    : AutomorphicForm.exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/3be84129-449a-54bf-b2ac-403eaa74e357
-- title:
--   Archimedean K-finite induced vectors as local zeta sections
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$, and let the completion $L = F_w$ carry its Borel measurable structure together with an additive Haar measure $\mu_a$. Let $\eta_1,\eta_2 : L^\times \to \mathbb{C}^\times$ be group homomorphisms that are unitary ($\|\eta_i(x)\| = 1$ for all $x$) and continuous as $\mathbb{C}$-valued functions, and let $f : \mathrm{GL}_2(L) \to \mathbb{C}$ be continuous and such that the right translates $x \mapsto f(xk)$, for $k$ ranging over the subgroup of row isometries — those $k$ with $\|\det k\| = 1$ and $\|x k_{00} + y k_{10}\|^2 + \|x k_{01} + y k_{11}\|^2 = \|x\|^2 + \|y\|^2$ for all $x,y \in L$ — all lie in the span of one finite set of functions. Assume further that $f(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,f(g)$ whenever $b$ has $b_{10} = 0$ and both $b$ and $g$ are row isometries (here $b_{00}, b_{11}$ are read as units of $L$ via `borelDiagFst`, `borelDiagSnd`). Then there exist $m \in \mathbb{N}$, functions $\Phi_j : L^2 \to \mathbb{C}$ and entire functions $e_j : \mathbb{C} \to \mathbb{C}$, $j \in \mathrm{Fin}\,m$, such that each $\Phi_j(y)$ is the value at $(\iota_w(y_0), \iota_w(y_1), \overline{\iota_w(y_0)}, \overline{\iota_w(y_1)})$ of a polynomial in four complex variables, times $\exp(-\pi \sum_i \|y_i\|^2)$, where $\iota_w =$ `Completion.extensionEmbedding w`, and such that for every $z$ with $\operatorname{Re} z > 0$ and every row isometry $k$,
--   $$\sum_{j} e_j(z)\,\eta_1(\det k)\, Z\bigl(t \mapsto \Phi_j(t k_{10}, t k_{11}),\, \eta_1\eta_2^{-1},\, z\bigr) = f(k),$$
--   where $Z(\varphi, \chi, z) = \int \varphi(x)\,\chi(x)\,|x|^z\,d^\times x$ is `localZeta`, the integral against $\mu_a$ restricted to $L \setminus \{0\}$ with density $|x|^{-1}$, $|\cdot|$ being the module given by the distributive Haar character and $\chi$ extended by $0$ at $0$.
--
--   This is Lemma 5.13 of Jacquet–Langlands and its complex analogue, localised at a single archimedean place: every $K$-finite vector in the representation of $\mathrm{GL}_2(F_w)$ induced from the pair of characters $(\eta_1,\eta_2)$ is recovered on the row-isometry subgroup as a finite combination, with entire coefficient functions, of Tate local zeta integrals of polynomial-times-Gaussian functions along the bottom row. It feeds the adelic statement [`AutomorphicForm.exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite`](thm.html#AutomorphicForm.exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite), where the archimedean places are combined, and is proved by splitting according to whether $w$ is real or complex.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite.lean

import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell.TateLocal

theorem AutomorphicForm.exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion]
    (μa : Measure w.Completion) [μa.IsAddHaarMeasure]
    (η₁ η₂ : (w.Completion)ˣ →* ℂˣ)
    (_h₁ : ∀ x, ‖((η₁ x : ℂˣ) : ℂ)‖ = 1) (_h₂ : ∀ x, ‖((η₂ x : ℂˣ) : ℂ)‖ = 1)
    (_h₁c : Continuous fun x : (w.Completion)ˣ => ((η₁ x : ℂˣ) : ℂ))
    (_h₂c : Continuous fun x : (w.Completion)ˣ => ((η₂ x : ℂˣ) : ℂ))
    (f : GL (Fin 2) w.Completion → ℂ) (_hfc : Continuous f)
    (_hfK : RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) f)
    (_hfB : ∀ (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion), IsRowIsometry b →
        ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f (b * g) = ((η₁ (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((η₂ (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ) * f g) :
    ∃ (m : ℕ) (Φ : Fin m → (Fin 2 → w.Completion) → ℂ) (e : Fin m → ℂ → ℂ),
      (∀ j, Differentiable ℂ (e j)) ∧
      (∀ j, ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ, ∀ y : Fin 2 → w.Completion,
        Φ j y = MvPolynomial.eval
              (Sum.elim (fun i => Completion.extensionEmbedding w (y i))
                (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (y i)))) P
            * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖y i‖ ^ 2 : ℝ)) : ℂ))) ∧
      ∀ z : ℂ, 0 < z.re →
        ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
          (∑ j, e j z * (((η₁ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
              * localZeta μa (fun t => Φ j (fun i => t * (k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                  (η₁ * η₂⁻¹) z))
            = f k := by sorry
