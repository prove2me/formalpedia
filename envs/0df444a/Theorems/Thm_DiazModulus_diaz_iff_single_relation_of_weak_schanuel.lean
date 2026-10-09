-- Prove2me | Theorems.Thm_DiazModulus_diaz_iff_single_relation_of_weak_schanuel
-- name    : DiazModulus.diaz_iff_single_relation_of_weak_schanuel
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-09T09:01:01.652514+00:00
-- url     : https://prove2.me/theorems/8fd6a1b2-9aee-4669-9d18-07def040f128
-- title:
--   Under the n = 2 case of Kirby's weak Schanuel conjecture, Diaz's conjecture is equivalent to: t² + π² is transcendental for every real t ≠ 0 with e^t algebraic
-- statement:
--   The hypothesis `hWSC` is the case $n = 2$ of Kirby's weak Schanuel conjecture (Kirby 2018, Conj. 1.5): if $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(a, b, e^a, e^b) < 2$, then $ma + nb \in 2\pi i\mathbb{Z}$ for some integers $(m, n) \neq (0, 0)$. It is not the ``weak Schanuel'' of Calegari and Mazur, which is the algebraic independence of logarithms and would give Diaz's conjecture outright.
--
--   Under `hWSC`, Diaz's modulus conjecture (`DiazModulus.DiazModulusConjecture`) holds if and only if $t^2 + \pi^2$ is transcendental for every real $t \neq 0$ with $e^t$ algebraic. The forward implication holds without `hWSC`. So, under Kirby's weak form, the real half of (S) is not needed.
--
--   **Proof.** `DiazModulus.leaf_iff_one` says the single relation is equivalent to Diaz's implication for the $u$ off both axes with $e^u$ real and $\neq 1$; so Diaz's conjecture gives the relation unconditionally. Conversely, for a candidate $u$, `DiazModulus.candidate_im_mem_pi_rat_of_weak_schanuel` gives $\operatorname{Im} u = q\pi$ with $q \in \mathbb{Q}^\times$ and $\operatorname{Re} u \neq 0$. With $N$ the denominator of $q$, $v = Nu$ has $\operatorname{Im} v$ a non-zero multiple of $\pi$, so $e^v$ is real and $\neq 1$, and $|v| = N|u|$ is algebraic; `leaf_iff_one` makes $e^v$ transcendental, while $e^v = (e^u)^N$ is algebraic.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. The hypothesis is the case n = 2 of J. Kirby, Variants of Schanuel's conjecture, arXiv:1801.08765 (2018), Conj. 1.5. R7 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 9 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem diaz_iff_single_relation_of_weak_schanuel
    (hWSC : ∀ a b : ℂ,
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({a, b, Complex.exp a, Complex.exp b} : Set ℂ)) < 2 →
      ∃ m n k : ℤ, (m ≠ 0 ∨ n ≠ 0) ∧
        (m : ℂ) * a + (n : ℂ) * b = 2 * ((Real.pi : ℝ) : ℂ) * Complex.I * (k : ℂ)) :
    DiazModulusConjecture ↔
      ∀ t : ℝ, t ≠ 0 → IsAlgebraic ℚ ((Real.exp t : ℝ) : ℂ) →
        Transcendental ℚ ((t ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) := by
  sorry

end DiazModulus
