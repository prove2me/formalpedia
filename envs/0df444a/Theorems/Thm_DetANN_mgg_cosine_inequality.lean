-- Prove2me | Theorems.Thm_DetANN_mgg_cosine_inequality
-- name    : DetANN.mgg_cosine_inequality
-- status  : Proved
-- author  : @milia
-- created : 2026-11-14T21:25:02.435135+00:00
-- url     : https://prove2.me/theorems/f05c7fe4-fbcf-430a-888e-fb8d50384d6d
-- title:
--   Cosine form of the Gabber–Galil inequality
-- statement:
--   Let $m\ge1$, and let $\tilde u\in(-m/2,m/2]$ be the representative of $u\in\mathbb Z_m$. With $T_1^{-1}z=(z_1-2z_2,\,z_2)$ and $T_2^{-1}z=(z_1,\,z_2-2z_1)$: for every $G:\mathbb Z_m^2\to\mathbb R$ with $G\ge0$ and $G(0,0)=0$,
--
--   $$\sum_{z\in\mathbb Z_m^2}2G(z)\Bigl[G(T_2^{-1}z)\,\bigl|\cos(\pi\tilde z_1/m)\bigr|+G(T_1^{-1}z)\,\bigl|\cos(\pi\tilde z_2/m)\bigr|\Bigr]\le\frac{5\sqrt2}{2}\sum_{z\in\mathbb Z_m^2}G(z)^2.$$
--
--   This is the real form of the Fourier-side inequality `mgg_fourier_inequality`, obtained by taking moduli and using $|1+\omega^{-t}|=2|\cos(\pi t/m)|$. The cosine factors are small at high frequencies, and that is where the bound gains on the trivial constant $4$.
--
--   **Formalization Note.** $|\cos(\pi\tilde u/m)|$ does not depend on which integer representative of $u$ is used, so the choice of `valMinAbs` is immaterial. The hypothesis $G\ge0$ is kept so that the statement matches HLW's Theorem 8.8. However, the Lean proof submitted for this statement never uses it, and Lean flags it as an unused variable. So the inequality holds for every real-valued $G$ with $G(0,0)=0$, not only for nonnegative ones.
-- source:
--   Hoory, Linial, Wigderson, Expander graphs and their applications, Bull. Amer. Math. Soc. 43 (2006), 439–561, https://www.ams.org/journals/bull/2006-43-04/S0273-0979-06-01126-8/, §8.2, Theorem 8.8, eq. (13), p. 506

import Mathlib

namespace DetANN

/-- **The real cosine inequality** (HLW06 §8.2, Theorem 8.8, inequality (13)).
For nonnegative `G` on `ℤ_m²` with `G(0,0) = 0`, with `z̃ᵢ` the representative in `(-m/2, m/2]`. -/
theorem mgg_cosine_inequality (m : ℕ) [NeZero m] (G : ZMod m × ZMod m → ℝ)
    (hG : ∀ z, 0 ≤ G z) (hG0 : G 0 = 0) :
    ∑ z, 2 * G z * (G (z.1, z.2 - 2 * z.1) * |Real.cos (Real.pi * (z.1.valMinAbs : ℝ) / m)| +
        G (z.1 - 2 * z.2, z.2) * |Real.cos (Real.pi * (z.2.valMinAbs : ℝ) / m)|)
      ≤ 5 * Real.sqrt 2 / 2 * ∑ z, G z ^ 2 := by sorry

end DetANN
