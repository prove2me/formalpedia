-- Prove2me | Theorems.Thm_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
-- name    : Complex.hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/4d248dac-5270-51ac-8725-ad30d52557b4
-- title:
--   Gauss partial-fraction series for ψ on Re s>0
-- statement:
--   Let $s$ be a complex number with $\operatorname{Re} s > 0$. Then the family indexed by the natural numbers $k$ with terms $\dfrac{1}{k+1} - \dfrac{1}{k+s}$ is summable with sum $\psi(s) + \gamma$, where $\psi = \Gamma'/\Gamma$ is the complex digamma function `Complex.digamma` and $\gamma$ is the Euler–Mascheroni constant `Real.eulerMascheroniConstant`, coerced into $\mathbb{C}$. The assertion is a `HasSum`, so it carries both the unconditional (unordered) summability of the family $k \mapsto 1/(k+1) - 1/(k+s)$ and the identification of its sum; no ordering of $\mathbb{N}$ or choice of partial sums is involved. The hypothesis $\operatorname{Re} s > 0$ in particular keeps $s$ away from the non-positive integers, so that every term is defined. Equivalently, the terms equal $(s-1)/\bigl((k+1)(k+s)\bigr)$, which are $O_s(k^{-2})$. The classical identity holds for all $s \notin \{0,-1,-2,\dots\}$; the form recorded here is restricted to the right half-plane.
--
--   This is the Gauss partial-fraction (series) representation of the digamma function, $\psi(s) = -\gamma + \sum_{k \ge 0}\bigl(1/(k+1) - 1/(k+s)\bigr)$. It is used to bound $\psi$ on half-planes: it feeds [`Complex.exists_forall_norm_digamma_le_mul_log_of_le_re`](thm.html#Complex.exists_forall_norm_digamma_le_mul_log_of_le_re), which provides logarithmic growth estimates for $\psi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s))
      (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) := by sorry
