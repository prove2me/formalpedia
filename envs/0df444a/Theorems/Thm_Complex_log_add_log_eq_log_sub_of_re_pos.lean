-- Prove2me | Theorems.Thm_Complex_log_add_log_eq_log_sub_of_re_pos
-- name    : Complex.log_add_log_eq_log_sub_of_re_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/8daf8913-f570-59e6-8c5e-c365ab8d8d5e
-- title:
--   Branch rule for log on the right half-plane
-- statement:
--   Let $u,v,w$ be complex numbers with $\operatorname{Re} u>0$, $\operatorname{Re} v>0$ and $\operatorname{Re} w>0$, and suppose that $uv=-i\,w$. Then the principal logarithms (Mathlib's `Complex.log`, whose imaginary part lies in $(-\pi,\pi]$ and which sends $0$ to $0$) satisfy $$\log u+\log v=\log w-\frac{\pi i}{2},$$ where $\pi$ is the real constant `Real.pi` coerced into $\mathbb{C}$. Thus, under the stated half-plane conditions, the additive identity for the principal branch acquires exactly the correction term $-\pi i/2$ dictated by the factor $-i$ relating $uv$ to $w$, with no further integer multiple of $2\pi i$. All three positivity hypotheses are used: they confine $\arg u$, $\arg v$ and $\arg w$ to the open interval $(-\pi/2,\pi/2)$, which is what pins down the branch.
--
--   This is the elementary branch bookkeeping underlying the transformation behaviour of the logarithm of the Dedekind $\eta$-function: it is cited by [`ModularForm.logEta_specialLinearGroup_smul`](thm.html#ModularForm.logEta_specialLinearGroup_smul) to control the constant appearing when $\log\eta$ is transformed under an element of $\mathrm{SL}_2(\mathbb{Z})$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_log_add_log_eq_log_sub_of_re_pos.lean

import Mathlib.Analysis.SpecialFunctions.Complex.Log

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.log_add_log_eq_log_sub_of_re_pos {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re) (h : u * v = -Complex.I * w) : Complex.log u + Complex.log v = Complex.log w - Real.pi * Complex.I / 2 := by sorry
