-- Prove2me | Theorems.Thm_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top
-- name    : CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/0cbe4b5c-eeba-5656-89e0-61c7787773a0
-- title:
--   Rational fractions in j and Fricke functions span cusp forms
-- statement:
--   Let $N\ge 1$, and for $\tau\in\mathfrak H$ let $L_\tau$ be a period pair with $\omega_1=\tau$, $\omega_2=1$. Let $W$ satisfy $W_v(\tau)=(2\pi i)^{-2}\wp_{L_\tau}\big((\tilde v_0\tau+\tilde v_1)/N\big)$ for $v\in(\mathbb Z/N)^2$, where $\tilde v_i$ denotes the standard representative in $\{0,\dots,N-1\}$, let $\mathrm{fricke}_v(\tau)=-\big(E_4(\tau)E_6(\tau)/\Delta(\tau)\big)/2592\cdot W_v(\tau)$, and let $\mathrm{jf}(\tau)=E_4(\tau)^3/\Delta(\tau)$. Let $K$ be the intermediate field $\mathbb Q\big(e^{2\pi i/N}\big)$ of $\mathbb C$, let $\Gamma\le \mathrm{SL}_2(\mathbb Z)$ contain $\Gamma(N)$, and let $k\in\mathbb Z$ and $a,b,m\in\mathbb N$ satisfy $k+4a+6b=12m$. Consider the set of cusp forms $f$ of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb R)$ for which there are polynomials $P,Q$ over $\mathbb C$ in variables indexed by $\mathrm{Option}\,\{v\ne 0\}$ — one variable specialised to $\mathrm{jf}$, one to $\mathrm{fricke}_v$ for each nonzero $v$ — all of whose coefficients lie in $K$, such that the specialisation of $Q$ is not the zero function and, for every $\tau$, $f(\tau)E_4(\tau)^aE_6(\tau)^b\cdot Q(\mathrm{jf},(\mathrm{fricke}_v))(\tau)=\Delta(\tau)^m\cdot P(\mathrm{jf},(\mathrm{fricke}_v))(\tau)$. The assertion is that the $\mathbb C$-linear span of this set is the whole space of weight-$k$ cusp forms for $\Gamma$.
--
--   This is the rationality (base-change, or $q$-expansion principle) statement for cusp forms on a group between $\Gamma(N)$ and $\mathrm{SL}_2(\mathbb Z)$: the forms whose weight-zero companion $fE_4^aE_6^b/\Delta^m$ is a fraction in $j$ and the Fricke functions with coefficients in $\mathbb Q(\zeta_N)$ already span the full complex space, as in Shimura's treatment of the field of modular functions of level $N$. It is used to produce a basis of the space of cusp forms on $\Gamma_1(N)$ of even weight whose $q$-expansion coefficients lie in $\mathbb Q(\zeta_N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Complex Real UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m) :
    Submodule.span ℂ {f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k |
      ∃ P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ,
        (∀ mo, P.coeff mo ∈ K) ∧ (∀ mo, Q.coeff mo ∈ K) ∧
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) Q ≠ 0 ∧
        ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke v.1) Q τ =
          ModularForm.discriminant τ ^ m *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke v.1) P τ} = ⊤ := by sorry
