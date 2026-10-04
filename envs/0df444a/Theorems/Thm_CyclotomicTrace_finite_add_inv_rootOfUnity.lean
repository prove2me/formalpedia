-- Prove2me | Theorems.Thm_CyclotomicTrace_finite_add_inv_rootOfUnity
-- name    : CyclotomicTrace.finite_add_inv_rootOfUnity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T05:57:31.64285+00:00
-- url     : https://prove2.me/theorems/808595ab-056b-4e9a-b3d1-c4fdfbd427aa
-- title:
--   A finitely generated subring of ℝ contains only finitely many numbers z + 1/z with z a root of unity
-- statement:
--   Let $s$ be a finite set of real numbers and $R$ the subring of $\mathbb R$ it generates. Then only finitely many real numbers $r \in R$ can be written as $r = z + z^{-1}$ with $z$ a complex root of unity ($z^n = 1$ for some $n \ge 1$).
--
--   Equivalently, only finitely many of the numbers $2\cos(2\pi k / n)$ lie in $R$. Since the trace of an element of finite order of $\mathrm{SL}_2(\mathbb R)$ has this form, a finitely generated subgroup of $\mathrm{SL}_2(\mathbb R)$ has only finitely many traces of elements of finite order.
--
--   *Context.* This is the finiteness used in the proof of `DenseSL2.exists_elliptic_infinite_order_of_dense`.
-- source:
--   Standalone lemma, a step of the proof of DenseSL2.exists_elliptic_infinite_order_of_dense (the traces of elements of finite order of SL(2, R) are the numbers z + 1/z)

import Mathlib

namespace CyclotomicTrace

theorem finite_add_inv_rootOfUnity (s : Finset ℝ) :
    {r : ℝ | r ∈ Subring.closure (s : Set ℝ) ∧
      ∃ z : ℂ, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) ∧ (r : ℂ) = z + z⁻¹}.Finite := by
  sorry

end CyclotomicTrace
