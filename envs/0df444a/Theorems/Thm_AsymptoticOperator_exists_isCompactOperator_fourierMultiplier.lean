-- Prove2me | Theorems.Thm_AsymptoticOperator_exists_isCompactOperator_fourierMultiplier
-- name    : AsymptoticOperator.exists_isCompactOperator_fourierMultiplier
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T18:21:56.633556+00:00
-- url     : https://prove2.me/theorems/8bf6d0c1-1c10-4cfb-b936-dcfd82df7c4b
-- title:
--   A Fourier multiplier with decaying symbol is a compact operator on L²(S¹, ℝ²ⁿ)
-- statement:
--   Let $n\ge 0$ and let $m:\mathbb Z\to\mathbb C^{2n\times 2n}$ be a family of complex matrices that is conjugate-symmetric, $m_{-k}=\overline{m_k}$ (entrywise conjugate), for all $k\in\mathbb Z$. Suppose there are real numbers $c_k$ with $c_k\to 0$ as $|k|\to\infty$ (along the cofinite filter on $\mathbb Z$) such that
--   $$|m_k v|^2\le c_k\,|v|^2\qquad\text{for all }k\in\mathbb Z,\ v\in\mathbb C^{2n},$$
--   where $|v|^2=\sum_i|v_i|^2$. Then there is a compact bounded linear operator $T$ on $L^2(S^1,\mathbb R^{2n})$, $S^1=\mathbb R/\mathbb Z$ with its Haar probability measure, such that for every $g\in L^2$ and every $k\in\mathbb Z$ the $k$-th Fourier coefficient of $Tg$ is
--   $$\widehat{(Tg)}_k=m_k\,\hat g_k .$$
--
--   Role: a general compactness criterion for operators on $L^2(S^1,\mathbb R^{2n})$ that are diagonal in the Fourier basis, reusable throughout the spectral theory of asymptotic operators $A_S=-J_0\partial_t-S$ on the circle.
--
--   Formalization note: $L^2$ is `L2 n` and $\hat g_k$ is `coeff g k` from the `AsymptoticOperator_Setting` definition module (Fourier coefficients of the complexified function, in `Fin n ⊕ Fin n → ℂ`). The matrices act by `Matrix.mulVec`; conjugate symmetry is stated as `m (-k) = (m k).map (starRingEnd ℂ)`. Compactness is Mathlib's `IsCompactOperator`. The bound is stated with squared norms, $\sum_i\|(m_k v)_i\|^2\le c_k\sum_i\|v_i\|^2$, and $c_k\to0$ is `Filter.Tendsto c Filter.cofinite (nhds 0)`.
-- source:
--   Standard Fourier-multiplier fact; used for Hofer-Wysocki-Zehnder (GAFA 1995), §3, p. 285, and Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, §3.2

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder Matrix

/-- A Fourier multiplier on `L²(S¹, ℝ²ⁿ)` with a decaying symbol is a compact operator.
The symbol `m : ℤ → ℂ^{2n×2n}` is conjugate-symmetric (`m₋ₖ = m̄ₖ`, so that real functions go to
real functions), and `|mₖ v|² ≤ cₖ |v|²` with `cₖ → 0` as `|k| → ∞`. Then there is a compact
operator `T` on `L²` acting on Fourier coefficients by `(Tg)^ₖ = mₖ ĝₖ`. -/
theorem exists_isCompactOperator_fourierMultiplier {n : ℕ}
    (m : ℤ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hm : ∀ k, m (-k) = (m k).map (starRingEnd ℂ))
    (c : ℤ → ℝ) (hc : Filter.Tendsto c Filter.cofinite (nhds 0))
    (hbound : ∀ (k : ℤ) (v : Fin n ⊕ Fin n → ℂ),
      ∑ i, ‖(m k *ᵥ v) i‖ ^ 2 ≤ c k * ∑ i, ‖v i‖ ^ 2) :
    ∃ T : L2 n →L[ℝ] L2 n, IsCompactOperator T ∧
      ∀ (g : L2 n) (k : ℤ), coeff (T g) k = m k *ᵥ coeff g k := by sorry

end AsymptoticOperator
