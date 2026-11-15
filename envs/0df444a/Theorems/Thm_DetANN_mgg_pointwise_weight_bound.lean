-- Prove2me | Theorems.Thm_DetANN_mgg_pointwise_weight_bound
-- name    : DetANN.mgg_pointwise_weight_bound
-- status  : Proved
-- author  : @milia
-- created : 2026-11-14T21:25:19.349741+00:00
-- url     : https://prove2.me/theorems/413b56a2-781e-4da3-b842-e9cc579dfb93
-- title:
--   Pointwise weight bound for the Gabber–Galil inequality
-- statement:
--   Let $m\ge1$, let $\tilde u\in(-m/2,m/2]$ be the representative of $u\in\mathbb Z_m$, and let $\gamma=\gamma_{\sqrt2}$ be the weight of the definition `DetANN_MGGOrder`. Write $T_1(x,y)=(x+2y,\,y)$, $T_2(x,y)=(x,\,y+2x)$, $e_1=(1,0)$ and $e_2=(0,1)$, all modulo $m$. For every $z\in\mathbb Z_m^2$ with $z\ne0$,
--
--   $$\bigl|\cos(\pi\tilde z_1/m)\bigr|\bigl[\gamma(z,T_2z)+\gamma(z,T_2^{-1}z)\bigr]+\bigl|\cos(\pi\tilde z_2/m)\bigr|\bigl[\gamma(z,T_1z)+\gamma(z,T_1^{-1}z)\bigr]\le\frac{5\sqrt2}{2}.$$
--
--   This is HLW's term-by-term inequality (15), to which the cosine inequality `mgg_cosine_inequality` is reduced by applying $2ab\le\gamma a^2+\gamma^{-1}b^2$ edge by edge.
--
--   **Formalization Note.** HLW prove (15) only with $\alpha=5/4$, which gives the weaker constant $3.65$ (their (16) and Proposition 8.9). They state that "a different choice for $\alpha$ and a more careful analysis" yields $5\sqrt2/2$. This statement is (15) with $\alpha=\sqrt2$, the choice for which the bound $5\sqrt2/2$ holds.
-- source:
--   Hoory, Linial, Wigderson, Expander graphs and their applications, Bull. Amer. Math. Soc. 43 (2006), 439–561, https://www.ams.org/journals/bull/2006-43-04/S0273-0979-06-01126-8/, §8.2: inequality (15) with α = √2 (pp. 506–507), Proposition 8.9 and the remark after it (pp. 507–508); Gabber, Galil, Explicit constructions of linear-sized superconcentrators, J. Comput. System Sci. 22 (1981), 407–420

import Mathlib
import Definitions.Def_DetANN_MGGOrder

namespace DetANN

/-- **The local inequality** (HLW06 §8.2, inequality (15) with `α = √2`; Proposition 8.9).
For every `z ≠ 0` in `ℤ_m²`, the weights of the four moves `T₂^{±1}z`, `T₁^{±1}z`, damped by the
cosines of the fixed coordinate, sum to at most `5√2/2`. -/
theorem mgg_pointwise_weight_bound (m : ℕ) [NeZero m] (z : ZMod m × ZMod m) (hz : z ≠ 0) :
    |Real.cos (Real.pi * (z.1.valMinAbs : ℝ) / m)| *
        (mggWeight (Real.sqrt 2) z (z.1, z.2 + 2 * z.1) +
          mggWeight (Real.sqrt 2) z (z.1, z.2 - 2 * z.1)) +
      |Real.cos (Real.pi * (z.2.valMinAbs : ℝ) / m)| *
        (mggWeight (Real.sqrt 2) z (z.1 + 2 * z.2, z.2) +
          mggWeight (Real.sqrt 2) z (z.1 - 2 * z.2, z.2))
      ≤ 5 * Real.sqrt 2 / 2 := by sorry

end DetANN
