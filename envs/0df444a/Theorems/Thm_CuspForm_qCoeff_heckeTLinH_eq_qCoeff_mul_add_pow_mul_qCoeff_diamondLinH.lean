-- Prove2me | Theorems.Thm_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH
-- name    : CuspForm.qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/99f81b86-8dc8-5b60-a237-407ce934b913
-- title:
--   q-expansion of T_ℓ on cusp forms for Γ_H(M)
-- statement:
--   Let $M$ be a positive natural number, $H$ a subgroup of $(\mathbb{Z}/M)^{\times}$, $k$ an integer, and $\ell$ a prime with $\ell \nmid M$. Write $\Gamma_H(M)$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained as the image of those $\gamma \in \Gamma_0(M)$ whose lower-right entry reduces into $H$ modulo $M$. Let $f$ be a cusp form of weight $k$ for $\Gamma_H(M)$, and $n$ a natural number. The assertion is that the $n$-th coefficient of the $q$-expansion (with period $1$, i.e. in $q = e^{2\pi i \tau}$) of [`CuspForm.heckeTLinH k hℓ hℓM f`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) equals $$a_{n\ell}(f) + \ell^{\,k-1}\cdot\bigl(\text{$a_{n/\ell}(\langle \ell\rangle f)$ if $\ell \mid n$, and $0$ otherwise}\bigr),$$ where $a_m$ denotes the $m$-th such $q$-coefficient, $\ell^{k-1}$ is the integer power of $\ell$ viewed in $\mathbb{C}$, and $\langle\ell\rangle f$ is [`CuspForm.diamondLinH k`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132) applied to the unit [`CuspForm.unitOfPrimeNotDvd hℓ hℓM`](def/CuspForm_HeckeOperatorFormsGammaH.html#L42), namely the class of $\ell$ in $(\mathbb{Z}/M)^{\times}$. Since the stability predicates [`CuspForm.StableT M H k ℓ`](def/CuspForm_HeckeOperatorFormsGammaH.html#L85) and [`CuspForm.StableD M H k`](def/CuspForm_HeckeOperatorFormsGammaH.html#L72) hold unconditionally by [`CuspForm.stableT`](thm.html#CuspForm.stableT) and [`CuspForm.stableD`](thm.html#CuspForm.stableD), the two operators are the genuine ones: $T_\ell f = U_\ell f + f\mid_k\!\left(\sigma_\ell \begin{pmatrix}\ell&0\\0&1\end{pmatrix}\right)$, with $\sigma_\ell \in \Gamma_0(M)$ having lower-right entry congruent to $\ell$ modulo $M$, and $\langle d\rangle f = f\mid_k \sigma_d$.
--
--   This is the classical Fourier-coefficient formula $a_n(T_\ell f) = a_{n\ell}(f) + \ell^{k-1} a_{n/\ell}(\langle\ell\rangle f)$ for the Hecke operator at a prime $\ell$ not dividing the level, stated for $\Gamma_H(M)$ with no nebentypus hypothesis; for a form with character $\varepsilon$ it specialises to $a_{n\ell} + \varepsilon(\ell)\ell^{k-1}a_{n/\ell}$. It is used in the integrality and stability arguments for the lattice of forms with prescribed coefficients, in particular by the results showing that the Hecke generators and the diamond operators preserve membership in such coefficient conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH.lean

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ModularForm MatrixGroups

theorem CuspForm.qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(CuspForm.heckeTLinH k hℓ hℓM f)) n =
      ModularFormClass.qCoeff (⇑f) (n * ℓ) +
        (ℓ : ℂ) ^ (k - 1) *
          (if ℓ ∣ n then
            ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH k (CuspForm.unitOfPrimeNotDvd hℓ hℓM) f)) (n / ℓ)
           else 0) := by sorry
