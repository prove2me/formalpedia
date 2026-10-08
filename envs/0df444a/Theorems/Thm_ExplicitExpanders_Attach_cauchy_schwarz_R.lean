-- Prove2me | Theorems.Thm_ExplicitExpanders_Attach_cauchy_schwarz_R
-- name    : ExplicitExpanders.Attach.cauchy_schwarz_R
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:13:58.988727+00:00
-- url     : https://prove2.me/theorems/de81c2ac-772b-4a74-9495-b2fe82c81323
-- title:
--   Cauchy–Schwarz display: $|\sum_{V}f|^2=|\sum_{R}f|^2\le|R|\sum_{R}f^2$ when $\sum_U f=0$ (Section 2.4)
-- statement:
--   Let $V$ be a finite set, let $R$ be a set of $r$ further elements, and let $f$ be a real function on $U=V\cup R$ (disjoint union) with $\sum_{u\in U} f(u)=0$. Then
--   $$\Big|\sum_{u\in V} f(u)\Big|^2=\Big|\sum_{u\in R} f(u)\Big|^2\le |R|\sum_{u\in R} f^2(u).$$
--
--   The equality holds because the two partial sums are negatives of each other, and the inequality is the Cauchy–Schwarz inequality. In the proof of Theorem 1.2 this shows that a unit vector orthogonal to the constant vector on $U$ has only a small component along the constant vector of the old vertex set $V$, since $|R|=r=o(m)$.
--
--   **Formalization Note** The paper also uses $\|f\|_2=1$ to write $|R|\sum_{u\in R}f^2(u)\le |R|$; the statement keeps the unnormalised form, from which that follows.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 9, Section 2.4, unnumbered display after (2) ("By Cauchy-Schwarz ...")

import Mathlib

namespace ExplicitExpanders.Attach

/-- The Cauchy–Schwarz display (arXiv:2003.11673v1, §2.4, p. 9): for a real function `f` on
`U = V ⊕ R`, `R = Fin r`, with `∑_{u ∈ U} f(u) = 0`, one has
`|∑_{u∈V} f(u)|² = |∑_{u∈R} f(u)|² ≤ |R| ∑_{u∈R} f(u)²`. -/
theorem cauchy_schwarz_R {V : Type*} [Fintype V] {r : ℕ} (f : V ⊕ Fin r → ℝ)
    (hf : ∑ u, f u = 0) :
    (∑ v, f (Sum.inl v)) ^ 2 = (∑ i, f (Sum.inr i)) ^ 2 ∧
      (∑ i, f (Sum.inr i)) ^ 2 ≤ (r : ℝ) * ∑ i, f (Sum.inr i) ^ 2 := by sorry

end ExplicitExpanders.Attach
