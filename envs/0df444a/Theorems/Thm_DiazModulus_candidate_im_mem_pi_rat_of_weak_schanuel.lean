-- Prove2me | Theorems.Thm_DiazModulus_candidate_im_mem_pi_rat_of_weak_schanuel
-- name    : DiazModulus.candidate_im_mem_pi_rat_of_weak_schanuel
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-09T09:00:44.874448+00:00
-- url     : https://prove2.me/theorems/aa7b3103-88ec-47f5-9bb1-86362797f1af
-- title:
--   Under the n = 2 case of Kirby's weak Schanuel conjecture, every candidate u has Re u ≠ 0 and Im u ∈ πℚ, Im u ≠ 0
-- statement:
--   The hypothesis `hWSC` is the case $n = 2$ of Kirby's weak Schanuel conjecture (Kirby 2018, Conj. 1.5): if $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(a, b, e^a, e^b) < 2$, then $ma + nb \in 2\pi i\mathbb{Z}$ for some integers $(m, n) \neq (0, 0)$. It is not the ``weak Schanuel'' of Calegari and Mazur, which is the algebraic independence of logarithms and would give Diaz's conjecture outright.
--
--   Let $u$ be a candidate for Diaz's conjecture (`DiazModulus.IsCandidate`: $u \neq 0$, $|u|$ and $e^u$ algebraic). Then $\operatorname{Re} u \neq 0$ and $\operatorname{Im} u = q\pi$ for some non-zero rational $q$. It concerns candidates, so it is vacuous if Diaz's conjecture holds.
--
--   **Proof.** A candidate is off both axes by Hermite–Lindemann (`DiazModulus.diaz_on_axes_of_hermite_lindemann`), so $\operatorname{Re} u \neq 0$ and $\operatorname{Im} u \neq 0$. Every generator of $\mathbb{Q}[u, \bar u, e^u, e^{\bar u}]$ is algebraic over $\mathbb{Q}[u]$ ($e^{\bar u} = \overline{e^u}$, and $\bar u$ is a root of $uX - |u|^2$), so the transcendence degree is at most $1 < 2$, and `hWSC` gives $mu + n\bar u = 2\pi ik$ with $(m, n) \neq 0$. The real part gives $n = -m \neq 0$, the imaginary part $\operatorname{Im} u = (k/m)\pi$, and $k \neq 0$.
--
--   **Novelty.** Not found in the sources read; it is short. Kirby (2018) does not mention Diaz's conjecture.
-- source:
--   Not found in the sources read. The hypothesis is the case n = 2 of J. Kirby, Variants of Schanuel's conjecture, arXiv:1801.08765 (2018), Conj. 1.5. R7 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 9 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_im_mem_pi_rat_of_weak_schanuel
    (hWSC : ∀ a b : ℂ,
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({a, b, Complex.exp a, Complex.exp b} : Set ℂ)) < 2 →
      ∃ m n k : ℤ, (m ≠ 0 ∨ n ≠ 0) ∧
        (m : ℂ) * a + (n : ℂ) * b = 2 * ((Real.pi : ℝ) : ℂ) * Complex.I * (k : ℂ))
    {u : ℂ} (h : IsCandidate u) :
    u.re ≠ 0 ∧ ∃ q : ℚ, q ≠ 0 ∧ u.im = (q : ℝ) * Real.pi := by
  sorry

end DiazModulus
