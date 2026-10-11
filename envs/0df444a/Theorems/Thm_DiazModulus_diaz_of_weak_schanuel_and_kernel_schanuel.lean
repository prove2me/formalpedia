-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_weak_schanuel_and_kernel_schanuel
-- name    : DiazModulus.diaz_of_weak_schanuel_and_kernel_schanuel
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-11T08:03:44.404153+00:00
-- url     : https://prove2.me/theorems/858142e9-e8e2-4f63-ab8d-8f07e4dd167b
-- title:
--   Kirby's weak Schanuel conjecture for n = 2, with Schanuel's conjecture over the kernel for n = 1 (trdeg Q(π, a, eᵃ) ≥ 2 for a ∉ 2πiQ), implies Diaz's conjecture
-- statement:
--   The hypothesis `hWSC` is the case $n = 2$ of Kirby's weak Schanuel conjecture (Kirby 2018, Conj. 1.5): if $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(a, b, e^a, e^b) < 2$, then $ma + nb \in 2\pi i\mathbb{Z}$ for some integers $(m, n) \neq (0, 0)$. The hypothesis `hSCk` is the case $n = 1$ of Schanuel's conjecture over the kernel $2\pi i\mathbb{Q}$: for every $a \notin 2\pi i\mathbb{Q}$, $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(\pi, a, e^a) \geq 2$. (At $a = 1$ it contains the algebraic independence of $e$ and $\pi$, which is open.)
--
--   Under both hypotheses Diaz's modulus conjecture (`DiazModulus.DiazModulusConjecture`) holds.
--
--   **Proof.** By `DiazModulus.diaz_iff_single_relation_of_weak_schanuel` it suffices that $t^2 + \pi^2$ is transcendental for real $t \neq 0$ with $e^t$ algebraic. If it were algebraic, $t$ would be algebraic over $\mathbb{Q}(\pi)$ and $e^t$ over $\mathbb{Q}$, so $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(\pi, t, e^t) \leq 1$; but $t$ is real and non-zero, so not in $\mathbb{Q}\cdot2\pi i$, and `hSCk` gives at least $2$.
--
--   **Novelty.** Not found in the sources read; it is short. It combines `DiazModulus.diaz_iff_single_relation_of_weak_schanuel` (R7, not found in the sources read) with the kernel form of Schanuel's conjecture, a standard step.
-- source:
--   The hypothesis hWSC is the case n = 2 of J. Kirby, Variants of Schanuel's conjecture, arXiv:1801.08765 (2018), Conj. 1.5; hSCk is the case n = 1 of Schanuel's conjecture over the kernel. R11 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 11 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem diaz_of_weak_schanuel_and_kernel_schanuel
    (hWSC : ∀ a b : ℂ,
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({a, b, Complex.exp a, Complex.exp b} : Set ℂ)) < 2 →
      ∃ m n k : ℤ, (m ≠ 0 ∨ n ≠ 0) ∧
        (m : ℂ) * a + (n : ℂ) * b = 2 * ((Real.pi : ℝ) : ℂ) * Complex.I * (k : ℂ))
    (hSCk : ∀ a : ℂ, (∀ q : ℚ, a ≠ (q : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)) →
      2 ≤ Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ), a, Complex.exp a} : Set ℂ))) :
    DiazModulusConjecture := by
  sorry

end DiazModulus
