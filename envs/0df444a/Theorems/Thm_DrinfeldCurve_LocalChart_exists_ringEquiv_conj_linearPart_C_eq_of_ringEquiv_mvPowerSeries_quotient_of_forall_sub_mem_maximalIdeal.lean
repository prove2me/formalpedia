-- Prove2me | Theorems.Thm_DrinfeldCurve_LocalChart_exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal
-- name    : DrinfeldCurve.LocalChart.exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/ab913f3e-1fcb-5805-a2f3-f66126ad3aaf
-- title:
--   Transport of a residually trivial automorphism through a Drinfeld chart
-- statement:
--   Fix a prime $q$, a complete discrete valuation ring $W$ (a domain, adically complete for its maximal ideal) with $\mathfrak m_W = (\varpi)$, and $f,u,v \in W[[X_0,X_1]]$ with $u,v$ units and $f - (X_0X_1^q - X_0^qX_1) \in (X_0,X_1)^{q+2}$. Put $S = W[[X_0,X_1]]/(\mathrm{C}(\varpi)v - fu)$ with quotient map $\mathrm{mk}_S$. Let $R$ be a local ring, adically complete for $\mathfrak m_R$ and with finite residue field, $e : R \xrightarrow{\sim} S$ a ring isomorphism, and $x_0,x_1 \in R$ with $\mathfrak m_R = (x_0,x_1)$, $e(x_0) = \mathrm{mk}_S(X_0)$, $e(x_1) = \mathrm{mk}_S(X_1)$. Let $\theta_0$ be a ring automorphism of $R$ with $\theta_0(r) \equiv r \pmod{\mathfrak m_R}$ for all $r$, fixing $e^{-1}(\mathrm{mk}_S(\mathrm{C}(\varpi)))$, and suppose $c \in R$ and $g \in M_2(\mathbb Z)$ satisfy $\theta_0(x_j) \equiv c\sum_i g_{ij}x_i \pmod{\mathfrak m_R^2}$ for $j = 0,1$, together with $c^{q+1} \equiv 1 \pmod{\mathfrak m_R}$. Let $P,P',P''$ be propositions with $P \to c \equiv 1 \pmod{\mathfrak m_R}$ and $P' \to P'' \to c \not\equiv 1 \pmod{\mathfrak m_R}$. Then there are a ring automorphism $\theta$ of $S$, an element $c' \in W$ and $M \in M_2(W)$ such that $\theta \circ e = e \circ \theta_0$; $\theta$ fixes $\mathrm{mk}_S(\mathrm{C}(w))$ for every $w \in W$; $\theta(\mathrm{mk}_S(X_j)) - \mathrm{mk}_S(\sum_i \mathrm{C}(M_{ij})X_i) \in (\mathrm{mk}_S(X_0),\mathrm{mk}_S(X_1))^2$ for $j = 0,1$; $c'^{\,q+1} \equiv 1$ and $M_{ij} \equiv c' g_{ij} \pmod{\mathfrak m_W}$; and $P \to c' \equiv 1$, $P' \to P'' \to c' \not\equiv 1 \pmod{\mathfrak m_W}$.
--
--   This is the transport step for the action of level structures on the formal neighbourhood of a supersingular point, presented in a two-variable Drinfeld chart $W[[X_0,X_1]]/(\varpi v - fu)$: an abstractly given residually trivial automorphism of a complete local ring isomorphic to the chart is converted into a $W$-linear automorphism of the chart whose linear part is a constant matrix over $W$ with prescribed reduction. It is used in the analysis of the integral two-chart models of modular curves at full level, the $W$-linearity coming from the rigidity statement [`IsLocalRing.ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span`](thm.html#IsLocalRing.ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_LocalChart_exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem DrinfeldCurve.LocalChart.exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : maximalIdeal W = Ideal.span {ϖ})
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (R : Type) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]
    (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C ϖ * v - f * u})
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (hx₀ : e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0)) (hx₁ : e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1))

    (θ₀ : R ≃+* R) (hres : ∀ r : R, θ₀ r - r ∈ maximalIdeal R)
    (hfix : θ₀ (e.symm (Ideal.Quotient.mk _ (MvPowerSeries.C ϖ))) = e.symm (Ideal.Quotient.mk _ (MvPowerSeries.C ϖ)))
    (c : R) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (hlin₀ : θ₀ x₀ - c * (((g 0 0 : ℤ) : R) * x₀ + ((g 1 0 : ℤ) : R) * x₁) ∈ (maximalIdeal R) ^ 2)
    (hlin₁ : θ₀ x₁ - c * (((g 0 1 : ℤ) : R) * x₀ + ((g 1 1 : ℤ) : R) * x₁) ∈ (maximalIdeal R) ^ 2)

    (hc : c ^ (q + 1) - 1 ∈ maximalIdeal R)
    (P P' P'' : Prop) (hP : P → c - 1 ∈ maximalIdeal R) (hP' : P' → P'' → c - 1 ∉ maximalIdeal R) :
    let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C ϖ * v - f * u})
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ϖ * v - f * u})
    ∃ (θ : S ≃+* S) (c' : W) (M : Matrix (Fin 2) (Fin 2) W),

      (∀ r : R, θ (e r) = e (θ₀ r)) ∧

      (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

      (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
          mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
        (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
      (c' ^ (q + 1) - 1 ∈ maximalIdeal W) ∧
      (∀ ii jj : Fin 2, M ii jj - c' * ((g ii jj : ℤ) : W) ∈ maximalIdeal W) ∧
      (P → c' - 1 ∈ maximalIdeal W) ∧
      (P' → P'' → c' - 1 ∉ maximalIdeal W) := by sorry
