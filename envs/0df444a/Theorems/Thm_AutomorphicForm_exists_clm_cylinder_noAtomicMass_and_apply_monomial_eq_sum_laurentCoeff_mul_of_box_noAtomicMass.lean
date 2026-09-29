-- Prove2me | Theorems.Thm_AutomorphicForm_exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass
-- name    : AutomorphicForm.exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/00e31f5b-8a97-5845-a319-3c4924fa21a8
-- title:
--   Pushing a torus functional to the table space along Hecke words
-- statement:
--   Let $K$ and $L$ be number fields, $S_L$ a finite set of finite places of $L$, and $\xi_L$ a homomorphism from the full subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$; write $\zeta_w$ for the complex number $\xi_L(\det(\mathrm{heckeGen}(\mathcal{O}_L,L,w)))$, the value of $\xi_L$ on the determinant of the diagonal $\mathrm{GL}_2(\mathbb{A}_L)$-element built from the uniformiser unit at $w$. Let $X\subseteq\prod_w(\mathbb{C}\times\mathbb{C})$ be compact and contain every $x$ with $x_w=0$ for $w\in S_L$ and, for $w\notin S_L$, $(x_w)_2=N(w)\zeta_w$, $\|(x_w)_1\|\le (N(w)+1)\sqrt{\|\zeta_w\|}$ and $\overline{(x_w)_1}=\overline{(x_w)_2}\,(x_w)_1/\|(x_w)_2\|$, where $N(w)=\mathrm{absNorm}(w)$ (the project's $\mathrm{cNorm}$). Let $T$ be a finite set of finite places of $K$ of size $d$, let $w'$ be a map of places which on $T$ avoids $S_L$ and is injective there, and let $s$ satisfy $s_v^2=\zeta_{w'_v}$ for $v\in T$. Let $\mu$ be a continuous linear functional on $C((\mathbb{R}/\mathbb{Z})^{d},\mathbb{C})$ with no atomic mass on boxes: for each $\tau$ and each $\varepsilon>0$ there are open sets $U_i\ni\tau_i$ such that $\|\mu g\|<\varepsilon$ for every continuous $g$ of sup-norm at most $1$ vanishing off $\prod_i U_i$; and let $c(n)=\mu(e)$ whenever $e\,\theta=\prod_i \mathrm{fourier}(n_i)(\theta_i)$. Then there is a continuous linear functional $\Delta$ on $C(X,\mathbb{C})$ which has no atomic mass on the cylinders cut out by the coordinates $w'_v$, $v\in T$ (the same $\varepsilon$-$U$ formulation, with $g$ required to vanish at points $y\in X$ having $y_{w'_v}\notin U_v$ for some $v\in T$), and which satisfies, for all $ks,js$ from places of $K$ to $\mathbb{N}$ and every $g\in C(X,\mathbb{C})$ with $g(x)=\prod_{v\in T}((x_{w'_v})_1)^{ks_v}\,(N(w'_v)^{-1}(x_{w'_v})_2)^{js_v}$ on $X$, $$\Delta g=\sum_{n}\Big(\prod_{i}(\sqrt{N(w'_{v_i})}\,s_{v_i})^{ks_{v_i}}\,\zeta_{w'_{v_i}}^{\,js_{v_i}}\;[(\mathsf{T}+\mathsf{T}^{-1})^{ks_{v_i}}]_{n_i}\Big)\,c(n),$$ the sum being over $n$ in the product of the integer intervals $[-ks_{v_i},ks_{v_i}]$, the bracket being the coefficient of the Laurent polynomial $(\mathsf{T}+\mathsf{T}^{-1})^{ks}$ over $\mathbb{C}$, and $v_i$ denoting the place of $T$ indexed by $i$ under `T.equivFin`.
--
--   This is the table push-forward step in the comparison of trace formulas along Hecke words in the cyclic base change argument for $\mathrm{GL}_2$: it transports a functional on the Satake torus, free of atomic mass on boxes, to a functional on the compact table space, free of atomic mass on cylinders, and computes its values on word monomials by Chebyshev–Laurent coefficients. It feeds the two downstream statements combining slot-family coefficients with unipotent-cell integrals and with the hyperbolic term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass.lean

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArithCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ComplexConjugate

theorem AutomorphicForm.exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
    (hw'S : ∀ v ∈ T, w' v ∉ SL)
    (hw'i : ∀ v ∈ T, ∀ v' ∈ T, w' v = w' v' → v = v')
    (s : HeightOneSpectrum (𝓞 K) → ℂ)
    (hs : ∀ v ∈ T, s v ^ 2 =
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (μ : C((Fin T.card → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ)
    (hμ : ∀ (τ : Fin T.card → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin T.card → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin T.card → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε)
    (c : (Fin T.card → ℤ) → ℂ)
    (hc : ∀ (n : Fin T.card → ℤ) (e : C((Fin T.card → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) → μ e = c n) :
    ∃ Δ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Δ g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (g : C(X, ℂ)),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
        Δ g =
          ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                  s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                  Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
                LaurentPolynomial ℂ).coeff (n i)) *
            c n := by sorry
