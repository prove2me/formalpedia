-- Prove2me | Theorems.Thm_AlmostPeriodic_isAlmostPeriodicOnStrip_sum_prod_of_periodic
-- name    : AlmostPeriodic.isAlmostPeriodicOnStrip_sum_prod_of_periodic
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:35:56.157552+00:00
-- url     : https://prove2.me/theorems/f60cca15-ffb6-4d09-bcbd-ecb8e36ea125
-- title:
--   Finite sums and products of vertically periodic holomorphic functions on a strip are almost periodic
-- statement:
--   **Sums and products of vertically periodic holomorphic functions are almost periodic.** Let $a,b\in\mathbb R$ and let $f_1,\dots,f_n$ be holomorphic functions on the open vertical strip $\mathbf C_{(a,b)}=\{a<\operatorname{Re}s<b\}$, each vertically periodic: there are real numbers $P_j\neq0$ with
--   $$f_j(s+iP_j)=f_j(s)\qquad(s\in\mathbf C_{(a,b)},\ 1\le j\le n).$$
--   The periods are arbitrary; they may be $\mathbb Q$-linearly independent, in which case $\sum_j f_j$ need not be periodic. Then
--   $$\sum_{j=1}^n f_j\qquad\text{and}\qquad\prod_{j=1}^n f_j$$
--   are almost periodic analytic functions on $\mathbf C_{(a,b)}$: holomorphic there, and almost periodic in the sense of Bohr uniformly on every closed substrip $\mathbf C_{[\alpha,\beta]}$, $a<\alpha\le\beta<b$.
--
--   This is the class of examples given in Masullo §7.1.1 (p. 312). It contains the partial Euler product (7.1.1.1), $\prod_{v\in S_f}(1-q_v^{-s-it_v})$, whose factors have the vertical periods $2\pi/\log q_v$. The paper studies its vertical recurrence and that of its reciprocal.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 312–313, §7.1.1 (examples of almost periodic functions: finite sums and finite products of vertically periodic functions; example (7.1.1.1)); classical reference: H. Bohr, Zur Theorie der fastperiodischen Funktionen I, II, III, Acta Math. 45 (1924), 46 (1925), 47 (1926) [Bohr1, Bohr2, Bohr3], and H. Bohr, Almost Periodic Functions, Chelsea Publishing Company, New York, 1947 (dated 1933 in the paper's bibliography) [Bohr4], cited by the paper at this spot (analytic almost periodic functions: [Bohr4, Appendix II, §104, p. 101]).

import Mathlib
import Definitions.Def_AlmostPeriodic_AnalyticStrip

open Filter Topology

set_option autoImplicit false

namespace AlmostPeriodic

theorem isAlmostPeriodicOnStrip_sum_prod_of_periodic
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (P : ι → ℝ) (a b : ℝ)
    (hf : ∀ j ∈ s, DifferentiableOn ℂ (f j) {z : ℂ | a < z.re ∧ z.re < b})
    (hP : ∀ j ∈ s, P j ≠ 0)
    (hper : ∀ j ∈ s, ∀ z : ℂ, a < z.re → z.re < b →
      f j (z + (P j : ℂ) * Complex.I) = f j z) :
    IsAlmostPeriodicOnStrip (fun z => ∑ j ∈ s, f j z) a b ∧
      IsAlmostPeriodicOnStrip (fun z => ∏ j ∈ s, f j z) a b := by sorry

end AlmostPeriodic
