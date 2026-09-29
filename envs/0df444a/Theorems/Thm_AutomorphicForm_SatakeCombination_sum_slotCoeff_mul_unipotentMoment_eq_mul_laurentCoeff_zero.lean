-- Prove2me | Theorems.Thm_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero
-- name    : AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/9a167548-e6dc-539b-8512-f06e27bc56a6
-- title:
--   Slot combination of unipotent moments at one place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let `ws` assign to every height-one prime $v$ of $\mathcal{O}_K$ a prime $w_v$ of $\mathcal{O}_L$ lying under $v$ (an element of `v.Extension (𝓞 L)`). Fix a height-one prime $v$ of $\mathcal{O}_K$, a height-one prime $w'$ of $\mathcal{O}_L$, complex numbers $\xi,\zeta,\sigma,s$, and natural numbers $k,j$. Write $f =$ `slotDeg K L ws v`, the inertia degree `v.asIdeal.inertiaDeg' (ws v).1.asIdeal`, and $N(\cdot)$ for `Ideal.absNorm`. Assume $\sigma^2 = N(v)\,\xi$ (with $N(v)\xi$ written as `HeckeEigensystem.cNorm v * ξ`), $\sqrt{N(w')}\,s = \sigma^{f}$, $\xi^{f} = \zeta$ and $N(w_v) = N(v)^{f}$. Then the sum, over the support of the multivariate polynomial `slotWord K L ws v k j` $=$ `satakePow f (X 0) (X 1)`$^k\cdot((X_1)^{f})^{j}$ in $\mathbb{C}[X_0,X_1]$, of the coefficients
--   $$\operatorname{coeff}_r(\mathrm{slotWord})\,N(v)^{r_1}/N(w_v)^{j}$$
--   multiplied by
--   $$\frac{1+(-1)^{r_0}}{2}\,\bigl(4N(v)\xi\bigr)^{\lfloor r_0/2\rfloor}\Bigl(\prod_{n<\lfloor r_0/2\rfloor}\frac{2n+1}{2n+2}\Bigr)\xi^{r_1},$$
--   the product being formed in $\mathbb{R}$ and then cast to $\mathbb{C}$, equals $(\sqrt{N(w')}\,s)^{k}\,\zeta^{j}$ times the degree-zero coefficient of $(T+T^{-1})^{k}$ in the Laurent polynomial ring over $\mathbb{C}$.
--
--   This is the one-place identity matching the slot coefficients attached to a prime $v$ against the even unipotent moments, expressed through the constant Laurent coefficient of $(t+t^{-1})^k$. It serves as the per-place input to the assembly over a family of places in [`AutomorphicForm.sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge`](thm.html#AutomorphicForm.sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge), where the family index set is a product of such supports and the family coefficient a product of the `slotCoeff`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (w' : HeightOneSpectrum (𝓞 L))
    (ξ ζ σr s : ℂ)
    (hσ : σr ^ 2 = HeckeEigensystem.cNorm v * ξ)
    (hs : ((Real.sqrt (Ideal.absNorm w'.asIdeal : ℝ) : ℂ) * s) = σr ^ SatakeCombination.slotDeg K L ws v)
    (hζ : ξ ^ SatakeCombination.slotDeg K L ws v = ζ)
    (hNws : Ideal.absNorm (ws v).1.asIdeal = Ideal.absNorm v.asIdeal ^ SatakeCombination.slotDeg K L ws v)
    (k j : ℕ) :
    ∑ r ∈ (SatakeCombination.slotWord K L ws v k j).support,
      SatakeCombination.slotCoeff K L ws v k j r *
        ((1 + (-1 : ℂ) ^ r 0) / 2 * (4 * (HeckeEigensystem.cNorm v * ξ)) ^ (r 0 / 2) *
          ((∏ n ∈ Finset.range (r 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) * ξ ^ r 1) =
      ((Real.sqrt (Ideal.absNorm w'.asIdeal : ℝ) : ℂ) * s) ^ k * ζ ^ j *
        ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff 0 := by sorry
