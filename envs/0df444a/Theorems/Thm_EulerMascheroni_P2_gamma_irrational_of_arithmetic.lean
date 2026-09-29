-- Prove2me | Theorems.Thm_EulerMascheroni_P2_gamma_irrational_of_arithmetic
-- name    : EulerMascheroni.P2.gamma_irrational_of_arithmetic
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-12T00:12:25.854185+00:00
-- url     : https://prove2.me/theorems/577d6ca7-de66-47f3-9ab9-318ce5d0fe5e
-- title:
--   Euler irrationality from explicit saddle estimates and arithmetic normalization
-- statement:
--   Assume the explicit oscillatory numerator limit and recurring noncancellation of the phase. Suppose nonzero real scalars c_n send P_(n+1),Q_(n+1) to integers p_n,q_n and c_n fModel_(n+1) tends to zero. Then Euler’s constant is irrational. The existence of such arithmetic scalars is not asserted: it is the missing arithmetic input, isolated from the analytic saddle limits.
--
--   **Connection to the Euler tree (12 September 2026).** The [explicit p=2 approximation branch](p2m:theorem/49746242-9b3e-4277-b5a4-6d00d752b173) studies the size of rational approximation errors. The proved [conditional irrationality bridge](p2m:theorem/577d6ca7-de66-47f3-9ab9-318ce5d0fe5e) shows that its numerator asymptotic, the proved [phase noncancellation](p2m:theorem/12d57034-9682-4ad6-a314-beba61cf6307), and a successful integer normalization would imply [irrationality of Euler’s constant](p2m:theorem/66a4e48a-f260-4615-92d3-686ca9356509). The required normalization consists of nonzero scalars c_n making both c_n P_(n+1) and c_n Q_(n+1) integers while c_n fModel_(n+1) tends to zero. No such scalars have been constructed. This is an explicit candidate route to the [vanishing integer linear forms leaf](p2m:theorem/7cfdfd24-8781-4193-a881-93684053aa63): one would select the infinitely many nonzero forms and normalize denominator signs. That connection is explanatory; it is not a submitted proof discharging the existence leaf. The mixed E/Gevrey lifting obligations in the [transcendence tree](p2m:theorem/1f5d0eac-7c79-43aa-b5f9-0cd302f56ad9) remain open. Irrationality alone would not prove transcendence.
-- source:
--   Classical integer-linear-form irrationality criterion, specialized to the explicit p=2 approximants of Van Assche–Wolfs, https://arxiv.org/html/2404.09799v3, section 5. The analytic and arithmetic hypotheses are explicit.

import Definitions.Def_eulerMascheroni_p2Approximation
import Mathlib.NumberTheory.Real.Irrational
open Filter Topology
open EulerMascheroni.P2

theorem EulerMascheroni.P2.gamma_irrational_of_arithmetic
    (hnum : Tendsto (fun n : ℕ => F (n+1) / fModel (n+1) - Real.sin (phase (n+1)))
      atTop (nhds 0))
    (hphase : ∃ᶠ n : ℕ in atTop, (1/2 : ℝ) ≤ |Real.sin (phase (n+1))|)
    (p q : ℕ → ℤ) (c : ℕ → ℝ)
    (hc : ∀ n, c n ≠ 0)
    (hp : ∀ n, (p n : ℝ) = c n * (P (n+1) : ℝ))
    (hq : ∀ n, (q n : ℝ) = c n * (Q (n+1) : ℝ))
    (hsmall : Tendsto (fun n => c n * fModel (n+1)) atTop (nhds 0)) :
    Irrational Real.eulerMascheroniConstant := by sorry
