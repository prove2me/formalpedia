-- Prove2me | Theorems.Thm_CuspForm_exists_gamma1_frickeRational_sigmaTransport
-- name    : CuspForm.exists_gamma1_frickeRational_sigmaTransport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/bed4bd6b-9cb1-5513-8169-ed5c77754e94
-- title:
--   Galois transport of Γ₁(N) cusp forms with Fricke expansions
-- statement:
--   Fix $N\ge 1$ (nonzero as a natural number). Let $L$ assign to each $\tau\in\mathfrak H$ a period pair with $\omega_1=\tau$, $\omega_2=1$; let $W$ be given by $W_v(\tau)=(2\pi i)^{-2}\wp\big((v_0\tau+v_1)/N;L(\tau)\big)$ for $v\in(\mathbb Z/N)^2$, the residues $v_0,v_1$ being read as their least non-negative lifts; let $\mathrm{fricke}_v(\tau)=-\big(E_4(\tau)E_6(\tau)/\Delta(\tau)\big)/2592\cdot W_v(\tau)$, and let $jf=E_4^3/\Delta$. Let $K=\mathbb Q\big(e^{2\pi i/N}\big)$ as an intermediate field of $\mathbb C/\mathbb Q$, let $s$ be a natural number coprime to $N$, and let $\varphi:K\to\mathbb C$ be a ring homomorphism sending any element of $K$ whose underlying complex number is $e^{2\pi i/N}$ to $e^{2\pi i s/N}$. Let $k\in\mathbb Z$ and $a,b,m\in\mathbb N$ satisfy $k+4a+6b=12m$, let $f$ be a cusp form of weight $k$ for $\Gamma_1(N)$, and let $P,Q$ be polynomials over $K$ in variables indexed by $\mathrm{Option}\,\{v\neq 0\}$, evaluated by sending the base point to $jf$ and $v$ to $\mathrm{fricke}_v$. Assume the evaluation of $Q$ (coefficients mapped into $\mathbb C$) is not the zero function, and that $f\cdot E_4^aE_6^b\cdot Q(jf,\mathrm{fricke}_v)=\Delta^m\cdot P(jf,\mathrm{fricke}_v)$ pointwise on $\mathfrak H$. Then there exists a cusp form $f'$ of weight $k$ for $\Gamma_1(N)$ such that, after applying $\varphi$ to coefficients and re-indexing the Fricke variables by $v\mapsto(v_0,sv_1)$, the evaluation of $Q$ is again not the zero function and $f'\cdot E_4^aE_6^b\cdot Q^{\varphi}=\Delta^m\cdot P^{\varphi}$ pointwise on $\mathfrak H$.
--
--   This is the weight-$k$, level-$\Gamma_1(N)$ instance of the classical transport of modular forms with $\mathbb Q(\zeta_N)$-rational Fricke expansions under the automorphism $\zeta_N\mapsto\zeta_N^{s}$ of the modular function field of level $N$, in the form given by Shimura. It feeds the comparison of $q$-expansion coefficients of cusp forms on $\Gamma_1(N)$ with their images under cyclotomic field automorphisms, used downstream as [`CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even`](thm.html#CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem CuspForm.exists_gamma1_frickeRational_sigmaTransport
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
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) τ =
      ModularForm.discriminant τ ^ m *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (P.map (algebraMap ↥K ℂ)) τ) :
    ∃ f' : CuspForm (CongruenceSubgroup.Gamma1 N) k,
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) ≠ 0 ∧
      ∀ τ : ℍ, f' τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
          MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
            o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) τ =
        ModularForm.discriminant τ ^ m *
          MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
            o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (P.map φ) τ := by sorry
