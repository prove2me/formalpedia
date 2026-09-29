-- Prove2me | Theorems.Thm_Complex_sqrt_mul_sqrt_eq_of_re_pos
-- name    : Complex.sqrt_mul_sqrt_eq_of_re_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/3d45d93c-741f-57ed-b1c3-177512a20d67
-- title:
--   Product rule for the principal square root across a quarter-turn
-- statement:
--   Let $u$, $v$, $w$ be complex numbers, each with strictly positive real part, and suppose that $uv = -i\,w$. Then, for the principal square root `Complex.sqrt` on $\mathbb{C}$ (that is, $a \mapsto a^{1/2}$ in the principal branch of the complex power), one has $$\sqrt{u}\,\sqrt{v} = \sqrt{-i}\,\sqrt{w}.$$ Note that the identity is stated with the factor $\sqrt{-i}$ on the right-hand side rather than with $\sqrt{uv} = \sqrt{-iw}$: the point is precisely that the two square roots $\sqrt{-i}\,\sqrt{w}$ and $\sqrt{-i\,w}$ need not agree, whereas the asserted equality holds under the three positivity hypotheses. All three hypotheses on the real parts are needed; the conclusion fails, for instance, when $u = v = e^{i\pi/3}$ and $w = i e^{2i\pi/3}$, where $\operatorname{Re} w < 0$.
--
--   This is the branch bookkeeping underlying the multiplier of $\sqrt{c\tau+d}$ in the transformation law of the Dedekind eta function: the positivity hypotheses encode that the relevant square roots lie in the sector $|\arg| < \pi/4$ and that a quarter-turn is absorbed by the explicit factor $\sqrt{-i}$. It is used in the proof of the eta transformation law under $\mathrm{SL}_2(\mathbb{Z})$, [`ModularForm.eta_specialLinearGroup_smul`](thm.html#ModularForm.eta_specialLinearGroup_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_sqrt_mul_sqrt_eq_of_re_pos.lean

import Mathlib.Analysis.RCLike.Sqrt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.sqrt_mul_sqrt_eq_of_re_pos {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re) (h : u * v = -Complex.I * w) : Complex.sqrt u * Complex.sqrt v = Complex.sqrt (-Complex.I) * Complex.sqrt w := by sorry
