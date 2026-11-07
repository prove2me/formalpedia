-- Prove2me | Theorems.Thm_ApproxGKR_eq_C_8_fourier
-- name    : ApproxGKR.eq_C_8_fourier
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:48.215985+00:00
-- url     : https://prove2.me/theorems/2265a9fe-325c-4d30-b348-3126aa70d228
-- title:
--   (C.8) — Fourier inversion and its error bound
-- statement:
--   Let $f$ be a complex polynomial of degree at most $D$, let $J>D$ and $\omega_J=\exp(2\pi i/J)$.
--   1. For $0\le a\le D$,
--   $$[X^a]f(X)=\frac1J\sum_{t=0}^{J-1}f(\omega_J^t)\,\omega_J^{-at}.$$
--   2. If $\tilde e_t$ are approximations with $|\tilde e_t-f(\omega_J^t)|\le e_{\mathrm{ev}}$ for every $t$, then for $0\le a\le D$
--   $$\Big|\frac1J\sum_{t=0}^{J-1}\tilde e_t\,\omega_J^{-at}-[X^a]f(X)\Big|\le e_{\mathrm{ev}}.$$
--
--   The honest prover recovers the coefficients of each round polynomial this way, with an error independent of $J$.
--
--   Differences from the source:
--   - generalization: J a power of two with D < J ≤ 2(D + 1) → any J > D; reason: the page's J is such a J
--   - encoding: ω_J^{−at} → (ω_J^t)^{−a}, written (root J t)⁻¹ ^ a; reason: the same number
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.2, eq. (C.8), p.35

import Mathlib
import Definitions.Def_ApproxGKR_root

namespace ApproxGKR

/-- **Equation (C.8): Fourier inversion and its error bound** (p.35).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.2, eq. (C.8), p.35: "For a polynomial `f` of degree at most `D`, choose a
power of two `J > D` with `J ≤ 2(D + 1)` and set `ωJ = exp(2πi/J)`. Then
`[X^a]f(X) = (1/J) Σ_{t=0}^{J−1} f(ω_J^t) ω_J^{−at}`, `0 ≤ a ≤ D`." "The coefficients
`J^{−1}ω_J^{−at}` have absolute sum one, so errors of at most `eev` in the evaluations contribute
at most `eev` to each recovered coefficient, independently of `J`".

1. The inversion formula, for every `0 ≤ a ≤ D`.
2. If `|ẽ_t − f(ω_J^t)| ≤ e_ev` for every `t`, then
   `|J^{−1} Σ_t ẽ_t ω_J^{−at} − [X^a]f| ≤ e_ev` for every `0 ≤ a ≤ D`.

**Formalization Note** `ω_J^t = root J t` and `ω_J^{−at} = (ω_J^t)^{−a}`. Stated for every
`J > D` (the page takes a power of two `J ≤ 2(D + 1)`). -/
theorem eq_C_8_fourier (f : Polynomial ℂ) (D J : ℕ) (hf : f.natDegree ≤ D) (hJ : D < J) :
    (∀ a, a ≤ D →
      f.coeff a = (J : ℂ)⁻¹ * ∑ t : Fin J, f.eval (root J t.val) * ((root J t.val)⁻¹) ^ a) ∧
    (∀ (eev : ℝ) (et : Fin J → ℂ), (∀ t, ‖et t - f.eval (root J t.val)‖ ≤ eev) →
      ∀ a, a ≤ D →
        ‖(J : ℂ)⁻¹ * ∑ t : Fin J, et t * ((root J t.val)⁻¹) ^ a - f.coeff a‖ ≤ eev) := by sorry

end ApproxGKR
