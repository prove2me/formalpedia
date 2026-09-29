-- Prove2me | Theorems.Thm_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C
-- name    : DrinfeldCurve.LocalChart.exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/33b2d231-856b-5743-9e05-c34b3cccf3e6
-- title:
--   Transporting initial-form unit conditions across Drinfeld chart isomorphisms
-- statement:
--   Let $q$ be a prime. For $i=1,2$ let $W_i$ be a discrete valuation ring that is a domain, with $\mathfrak m_{W_i}=(\pi_i)$ and $q\in\mathfrak m_{W_i}$, and let $f_i,u_i,v_i\in W_i[[X_0,X_1]]$ be two-variable power series with $u_i,v_i$ units and $f_i$ congruent to $X_0X_1^{q}-X_0^{q}X_1$ modulo $(X_0,X_1)^{q+2}$; write $S_i=W_i[[X_0,X_1]]/(C(\pi_i)v_i-f_iu_i)$. Let $\rho:W_1\to W_2$ be a ring homomorphism with $\rho(\pi_1)=\pi_2$, and let $\psi:S_1\to S_2$ be a ring isomorphism with $\psi(\overline{C(w)})=\overline{C(\rho w)}$ for all $w\in W_1$. Let $s\in S_1$, $a_0\in W_1$, $e_0\ge 1$, and let $h\in(X_0,X_1)^{e_0}\subset W_1[[X_0,X_1]]$ be such that $s-\overline{C(a_0)}=\bar h$, and such that for all $a,b\in W_1$ with at least one of $a,b$ outside $\mathfrak m_{W_1}$ and with $a^{q}b-ab^{q}\in\mathfrak m_{W_1}$, the element $\sum_{i=0}^{e_0}\mathrm{coeff}_{X_0^{i}X_1^{e_0-i}}(h)\,a^{i}b^{\,e_0-i}$ is a unit of $W_1$. Then there exists $h'\in(X_0,X_1)^{e_0}\subset W_2[[X_0,X_1]]$ satisfying the same unit condition over $W_2$ (for all $a,b\in W_2$ with at least one outside $\mathfrak m_{W_2}$ and $a^{q}b-ab^{q}\in\mathfrak m_{W_2}$) and such that $\psi(s)-\overline{C(\rho a_0)}=\bar{h'}$ in $S_2$.
--
--   This is the transport (rigidity) step for the local charts of the Drinfeld level structure: the property of a germ that, after subtracting a constant, it lies in the $(X_0,X_1)$-adic power $e_0$ with initial form invertible along the $\mathbb F_q$-rational directions is preserved by any isomorphism of chart rings compatible with constants. It is used in the full-level modular curve files, where one witness of this shape is promoted to a statement about arbitrary isomorphisms of completed stalks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem DrinfeldCurve.LocalChart.exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C
    (q : ℕ) [Fact q.Prime]
    (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
    (π₁ : W₁) (hπ₁ : maximalIdeal W₁ = Ideal.span {π₁}) (hq₁ : (q : W₁) ∈ maximalIdeal W₁)
    (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
    (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
    (W₂ : Type) [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂]
    (π₂ : W₂) (hπ₂ : maximalIdeal W₂ = Ideal.span {π₂}) (hq₂ : (q : W₂) ∈ maximalIdeal W₂)
    (f₂ u₂ v₂ : MvPowerSeries (Fin 2) W₂) (hu₂ : IsUnit u₂) (hv₂ : IsUnit v₂)
    (hf₂ : f₂ - DrinfeldCurve.LocalChart.drinfeldForm q W₂ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ (q + 2))
    (ρ : W₁ →+* W₂) (hρ : ρ π₁ = π₂)
    (ψ : (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C π₁ * v₁ - f₁ * u₁}) ≃+*
      (MvPowerSeries (Fin 2) W₂ ⧸ Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂}))
    (hψ : ∀ w : W₁, ψ (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (ρ w)))
    (s : MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C π₁ * v₁ - f₁ * u₁})
    (a₀ : W₁) (e₀ : ℕ) (he₀ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
    (hh : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀)
    (hunit : ∀ a b : W₁, (a ∉ maximalIdeal W₁ ∨ b ∉ maximalIdeal W₁) →
      a ^ q * b - a * b ^ q ∈ maximalIdeal W₁ →
        IsUnit (∑ i ∈ Finset.range (e₀ + 1),
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i)))
    (hs : s - Ideal.Quotient.mk _ (MvPowerSeries.C a₀) = Ideal.Quotient.mk _ h) :
    ∃ (h' : MvPowerSeries (Fin 2) W₂)
      (_ : h' ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ e₀),
      (∀ a b : W₂, (a ∉ maximalIdeal W₂ ∨ b ∉ maximalIdeal W₂) →
        a ^ q * b - a * b ^ q ∈ maximalIdeal W₂ →
          IsUnit (∑ i ∈ Finset.range (e₀ + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h' * a ^ i * b ^ (e₀ - i))) ∧
      ψ s - Ideal.Quotient.mk _ (MvPowerSeries.C (ρ a₀)) =
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂}) h' := by sorry
