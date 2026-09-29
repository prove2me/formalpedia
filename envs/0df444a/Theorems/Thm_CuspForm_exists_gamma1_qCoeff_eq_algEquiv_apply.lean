-- Prove2me | Theorems.Thm_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply
-- name    : CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/7a275869-93d6-51ee-9169-12c7366f435a
-- title:
--   Galois stability of K-rational cusp forms on Γ₁(N)
-- statement:
--   Let $N$ be a positive natural number and $k$ an integer. Let $K$ be an intermediate field of $\mathbb{C}/\mathbb{Q}$ which is assumed to equal the subfield $\mathbb{Q}(e^{2\pi i/N})$ generated over $\mathbb{Q}$ by $\exp(2\pi i/N)$, and let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $K$. Let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_1(N)$, and let $c : \mathbb{N} \to K$ be a sequence of elements of $K$ such that for every $m$ the $m$-th coefficient of the $q$-expansion of $f$ of width $1$, i.e. [`ModularFormClass.qCoeff f m`](def/FLTPrelim_Modularity.html#L19), the coefficient of $q^m$ in `qExpansion 1 f`, is the complex number $c_m$. The conclusion is that there exists a cusp form $f'$ of weight $k$ for $\Gamma_1(N)$ whose $q$-expansion coefficients of width $1$ are the images $\sigma(c_m)$, viewed in $\mathbb{C}$, for all $m$. No parity or positivity hypothesis on $k$ is imposed.
--
--   This is the Galois-equivariance statement for cyclotomic $q$-expansions: the space of cusp forms of weight $k$ on $\Gamma_1(N)$ whose coefficients lie in $\mathbb{Q}(\zeta_N)$ is stable under the coefficientwise action of $\mathrm{Gal}(\mathbb{Q}(\zeta_N)/\mathbb{Q})$. It is the descent input for [`CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`](thm.html#CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast), which produces a basis of cusp forms with rational $q$-expansion coefficients; the even-weight case is isolated in [`CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even`](thm.html#CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply (N : ℕ) [NeZero N] (k : ℤ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (σ : ↥K ≃ₐ[ℚ] ↥K) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k) (c : ℕ → ↥K)
    (hf : ∀ m : ℕ, ModularFormClass.qCoeff f m = (c m : ℂ)) :
    ∃ f' : CuspForm (CongruenceSubgroup.Gamma1 N) k,
      ∀ m : ℕ, ModularFormClass.qCoeff f' m = (σ (c m) : ℂ) := by sorry
