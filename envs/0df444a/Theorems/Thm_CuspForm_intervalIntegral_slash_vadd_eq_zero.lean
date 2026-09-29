-- Prove2me | Theorems.Thm_CuspForm_intervalIntegral_slash_vadd_eq_zero
-- name    : CuspForm.intervalIntegral_slash_vadd_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/07b0c90c-5f22-5f70-9de5-451c91edf381
-- title:
--   Vanishing horocycle integral of a cusp form at every cusp
-- statement:
--   Let $M$ be a natural number with $M \neq 0$, let $k$ be an integer, and let $h$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_1(M) \le \mathrm{SL}_2(\mathbb{Z})$ in the sense of Mathlib's `CuspForm`, i.e. a holomorphic function on the upper half-plane $\mathbb{H}$ which is invariant under the weight-$k$ slash action of $\Gamma_1(M)$ and vanishes at $i\infty$ after translating by any element of $\mathrm{SL}_2(\mathbb{Z})$. Let $\rho \in \mathrm{SL}_2(\mathbb{Z})$, viewed through the coercion into $\mathrm{GL}_2(\mathbb{R})$, and let $z \in \mathbb{H}$. The assertion is that the Bochner interval integral over $s \in [0, M]$ of the complex number $(h \mid_k \rho)(s +\!\!\cdot\, z)$, where $s +\!\!\cdot\, z$ denotes the additive action of the real number $s$ on $\mathbb{H}$ by horizontal translation and $\mid_k$ is the weight-$k$ slash action, equals $0$: $$\int_0^M (h \mid_k \rho)(s + z)\,\mathrm{d}s = 0 .$$ The conclusion holds for every base point $z$, the length of the interval of integration being the level $M$ rather than the width of the cusp $\rho\infty$.
--
--   This is the vanishing of the constant Fourier coefficient of a cusp form at an arbitrary cusp $\rho\infty$, expressed as the mean of $h \mid_k \rho$ over a horocycle of length $M$. It is used in the verification that the adelic lift of a cusp form on $\Gamma_1(M)$ is cuspidal, where the cuspidality condition appears precisely as the vanishing of such unipotent period integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_intervalIntegral_slash_vadd_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.intervalIntegral_slash_vadd_eq_zero
    {M : ℕ} [NeZero M] {k : ℤ} (h : CuspForm (CongruenceSubgroup.Gamma1 M) k) (ρ : SL(2, ℤ))
    (z : UpperHalfPlane) :
    ∫ s in (0 : ℝ)..(M : ℝ), ((⇑h) ∣[k] (ρ : GL (Fin 2) ℝ)) (s +ᵥ z) = 0 := by sorry
