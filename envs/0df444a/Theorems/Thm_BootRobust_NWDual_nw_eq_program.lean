-- Prove2me | Theorems.Thm_BootRobust_NWDual_nw_eq_program
-- name    : BootRobust.NWDual.nw_eq_program
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:23.164296+00:00
-- url     : https://prove2.me/theorems/5896d2c4-9fa5-4b15-a2f3-b5316b04ce78
-- title:
--   B.3, p. 27 — the Nadaraya–Watson estimate is the maximum of an (s, P) program with a single feasible point
-- statement:
--   Let $D\in\mathcal D_n$ be a distribution on the finite support $\Omega_n$, let $w_i>0$ be positive weights and $\ell_i$ arbitrary losses. Then the Nadaraya–Watson estimate
--   $$E^n_D[\ell]=\frac{\sum_i w_i\ell_iD_i}{\sum_i w_iD_i}$$
--   is the maximum of the program
--   $$\max_{s>0,\,P}\ \sum_i w_i\ell_iP_i\quad\text{s.t.}\quad P_i=D_i\,s\ \ \forall i,\qquad \sum_iP_i=s,\qquad\sum_iw_iP_i=1 .$$
--   The maximum is attained; in fact the only feasible point is $s=1/\sum_iw_iD_i$, $P=sD$.
--
--   This rewrites the ratio estimator as a linear objective over a cone, the first step towards the perspective program of Corollary 1.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, B.3 (proof of Corollary 1), p. 27, first display

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

namespace BootRobust.NWDual

/-- B.3, p. 27: the Nadaraya–Watson estimate (19) at `D ∈ Dₙ` is the maximum of the linear
program over `s > 0` and `P` with `P = s · D`, `∑ P = s` and `∑ w P = 1`. -/
theorem nw_eq_program {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (ℓ : ι → ℝ) :
    IsGreatest {x : ℝ | ∃ (s : ℝ) (P : ι → ℝ), 0 < s ∧ (∀ i, P i = D i * s) ∧
        ∑ i, P i = s ∧ ∑ i, w i * P i = 1 ∧ x = ∑ i, w i * ℓ i * P i}
      (BootRobust.Perf.nwEst w ℓ D) := by sorry

end BootRobust.NWDual
