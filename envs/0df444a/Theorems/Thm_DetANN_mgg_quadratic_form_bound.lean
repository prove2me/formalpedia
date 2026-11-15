-- Prove2me | Theorems.Thm_DetANN_mgg_quadratic_form_bound
-- name    : DetANN.mgg_quadratic_form_bound
-- status  : Proved
-- author  : @milia
-- created : 2026-11-14T21:25:03.002866+00:00
-- url     : https://prove2.me/theorems/74c60b88-d2dc-4694-9e15-0c45fd173569
-- title:
--   Gabber–Galil quadratic-form bound on $\mathbb Z_m^2$
-- statement:
--   Let $m\ge1$. Write $T_1(x,y)=(x+2y,\,y)$, $T_2(x,y)=(x,\,y+2x)$, $e_1=(1,0)$ and $e_2=(0,1)$, all modulo $m$. For every $f:\mathbb Z_m^2\to\mathbb R$ with $\sum_z f(z)=0$,
--
--   $$\Bigl|\sum_{z\in\mathbb Z_m^2} f(z)\bigl[f(T_1z)+f(T_1z+e_1)+f(T_2z)+f(T_2z+e_2)\bigr]\Bigr|\le\frac{5\sqrt2}{2}\sum_{z\in\mathbb Z_m^2} f(z)^2.$$
--
--   The four maps are the forward moves of the 8-regular Margulis–Gabber–Galil graph, and the left side is half the quadratic form $\langle f,Af\rangle$ of its adjacency matrix $A$. So the statement bounds every nontrivial eigenvalue of $A$ by $5\sqrt2$ in absolute value. That is the Gabber–Galil bound behind the milestone `mgg_spectral_bound`.
--
--   **Formalization Note.** HLW's Theorem 8.3 is printed one-sided. It is stated here with an absolute value, which the bound on $\|Wf\|$ requires because it must also control the most negative eigenvalue. This two-sided form is what HLW's argument establishes, since their Theorem 8.7 bounds a modulus.
-- source:
--   Hoory, Linial, Wigderson, Expander graphs and their applications, Bull. Amer. Math. Soc. 43 (2006), 439–561, https://www.ams.org/journals/bull/2006-43-04/S0273-0979-06-01126-8/, §8, Theorem 8.3, eq. (12), p. 504 (two-sided form); Gabber, Galil, Explicit constructions of linear-sized superconcentrators, J. Comput. System Sci. 22 (1981), 407–420; Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission, Appendix B, p.20

import Mathlib

namespace DetANN

/-- **The MGG quadratic-form bound** (HLW06 §8, Theorem 8.3, two-sided form; [GG81]).
For mean-zero `f` on `ℤ_m²`, the sum of `f(z)` times the four forward MGG neighbours
`T₁z, T₁z + e₁, T₂z, T₂z + e₂` is at most `(5√2/2)‖f‖²` in absolute value. -/
theorem mgg_quadratic_form_bound (m : ℕ) [NeZero m] (f : ZMod m × ZMod m → ℝ)
    (hf : ∑ z, f z = 0) :
    |∑ z, f z * (f (z.1 + 2 * z.2, z.2) + f (z.1 + (2 * z.2 + 1), z.2) +
        f (z.1, z.2 + 2 * z.1) + f (z.1, z.2 + (2 * z.1 + 1)))|
      ≤ 5 * Real.sqrt 2 / 2 * ∑ z, f z ^ 2 := by sorry

end DetANN
