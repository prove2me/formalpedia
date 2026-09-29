-- Prove2me | Theorems.Thm_EulerMascheroni_P2_int_linear_forms_of_primitive_saving
-- name    : EulerMascheroni.P2.int_linear_forms_of_primitive_saving
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-12T19:44:17.532223+00:00
-- url     : https://prove2.me/theorems/0fcb44d4-d914-4c38-a95d-bda94aa4a98e
-- title:
--   Integer linear forms from phase-compatible primitive saving
-- statement:
--   Assume $Q_n>0$ for every $n$ and the P2 oscillatory asymptotic
--
--   $$\frac{F_{n+1}}{\operatorname{fModel}(n+1)}-\sin(\operatorname{phase}(n+1))\longrightarrow0.$$
--
--   Write $b_n/a_n=P_n/Q_n$ in lowest terms, $a_n>0$, and $c_n=a_n/Q_n$. Suppose also that, for every $\varepsilon>0$ and every $N$, some $n\ge N$ has
--
--   $$|\sin(\operatorname{phase}(n+1))|\ge\tfrac12,
--   \qquad c_{n+1}\operatorname{fModel}(n+1)<\varepsilon.$$
--
--   Then there exist integer sequences $p_k,q_k$, with $q_k>0$, such that
--
--   $$q_k\gamma-p_k\ne0\quad\text{for every }k,
--   \qquad q_k\gamma-p_k\longrightarrow0.$$
--
--   This is a conditional theorem. It constructs the integer forms from reduced rational approximants on a selected subsequence; it does not assert the arithmetic-saving hypothesis. Phase noncancellation and small normalization must hold jointly, not merely on two unrelated infinite sets.
-- source:
--   Derived auxiliary results for the p=2, x=1 family in Van Assche–Wolfs, Rational approximation of Euler’s constant using multiple orthogonal polynomials, arXiv:2404.09799v3, Section 5, displayed binomial formula for F_(n;2)^(I|p), https://arxiv.org/html/2404.09799v3#S5. The reduced-fraction normalization and conditional subsequence criterion are elementary deductions supplied here, not named statements or arithmetic-saving claims in that paper.

import Definitions.Def_eulerMascheroni_p2PrimitiveNormalization
open Filter Topology
open EulerMascheroni.P2

theorem EulerMascheroni.P2.int_linear_forms_of_primitive_saving
    (hQ : ∀ n, 0 < Q n)
    (hnum : Tendsto (fun n : ℕ => F (n+1) / fModel (n+1) - Real.sin (phase (n+1)))
      atTop (nhds 0))
    (hsave : PrimitiveSaving) :
    ∃ p q : ℕ → ℤ, (∀ n, 0 < q n) ∧
      (∀ n, (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ) ≠ 0) ∧
      Tendsto (fun n => (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ))
        atTop (nhds 0)  := by sorry
