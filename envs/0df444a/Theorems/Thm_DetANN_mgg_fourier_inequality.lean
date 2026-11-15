-- Prove2me | Theorems.Thm_DetANN_mgg_fourier_inequality
-- name    : DetANN.mgg_fourier_inequality
-- status  : Proved
-- author  : @milia
-- created : 2026-11-14T21:25:03.11575+00:00
-- url     : https://prove2.me/theorems/e28b9d66-97d1-4959-ad79-30dfa98c3611
-- title:
--   Fourier-side Gabber–Galil inequality
-- statement:
--   Let $m\ge1$ and $\omega=e^{2\pi i/m}$, so $\omega^t$ is well defined for $t\in\mathbb Z_m$. Write $T_1^{-1}z=(z_1-2z_2,\,z_2)$ and $T_2^{-1}z=(z_1,\,z_2-2z_1)$. For every $F:\mathbb Z_m^2\to\mathbb C$ with $F(0,0)=0$,
--
--   $$\Bigl|\sum_{z\in\mathbb Z_m^2}\overline{F(z)}\bigl[F(T_2^{-1}z)(1+\omega^{-z_1})+F(T_1^{-1}z)(1+\omega^{-z_2})\bigr]\Bigr|\le\frac{5\sqrt2}{2}\sum_{z\in\mathbb Z_m^2}|F(z)|^2.$$
--
--   This is the frequency-side form of the Gabber–Galil bound. Under the Fourier transform on $\mathbb Z_m^2$, the translations by $e_1$ and $e_2$ become the phase factors $1+\omega^{-t}$, and the shears become their inverse transposes. Applied to $F=\hat f$, the inequality yields the quadratic-form bound `mgg_quadratic_form_bound`.
--
--   **Formalization Note.** $\omega^t$ is Mathlib's `ZMod.stdAddChar t` $=\exp(2\pi i t/m)$. As in HLW, the inequality is stated for every $F$, not only for Fourier transforms.
-- source:
--   Hoory, Linial, Wigderson, Expander graphs and their applications, Bull. Amer. Math. Soc. 43 (2006), 439–561, https://www.ams.org/journals/bull/2006-43-04/S0273-0979-06-01126-8/, §8.2, Theorem 8.7, p. 505

import Mathlib

namespace DetANN

/-- **The Fourier-side inequality** (HLW06 §8.2, Theorem 8.7). For every
`F : ℤ_m² → ℂ` with `F(0,0) = 0`, with `ω^t = stdAddChar t`,
`T₂⁻¹z = (z₁, z₂ - 2z₁)` and `T₁⁻¹z = (z₁ - 2z₂, z₂)`. -/
theorem mgg_fourier_inequality (m : ℕ) [NeZero m] (F : ZMod m × ZMod m → ℂ) (hF : F 0 = 0) :
    ‖∑ z, starRingEnd ℂ (F z) *
        (F (z.1, z.2 - 2 * z.1) * (1 + ZMod.stdAddChar (-z.1)) +
          F (z.1 - 2 * z.2, z.2) * (1 + ZMod.stdAddChar (-z.2)))‖
      ≤ 5 * Real.sqrt 2 / 2 * ∑ z, ‖F z‖ ^ 2 := by sorry

end DetANN
