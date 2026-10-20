-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_corollary_6_8
-- name    : DynkinAsymInfo.Linear.corollary_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:33.964028+00:00
-- url     : https://prove2.me/theorems/9a0b3e88-5884-45f0-becf-6589ea15d1fd
-- title:
--   Corollary 6.8 — upper bound on the lower threshold
-- statement:
--   Under Assumption 6.2, $\varepsilon>0$, $0<A<B$, and every equation and boundary condition of the $C^2$ boundary-value problem (85), the lower threshold obeys
--   $$A\le-\frac{\mu_0}{\mu_1}.$$
--   The bound restricts the possible location of the candidate stopping boundary. The $0<A<B$ hypothesis is implicit in the source's use of (85).
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, p. 23, Corollary 6.8, (85)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_Model

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, p. 23, Corollary 6.8.
The hypotheses spell out (85), including its implicit `0<A<B` domain. -/
theorem corollary_6_8 (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (eps : ℝ) (heps : 0 < eps) (A B : ℝ) (hAB : 0 < A ∧ A < B)
    (v : ℝ → ℝ) (hC2 : ContDiffOn ℝ 2 v (Set.Icc A B))
    (hODE : ∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv v) phi +
      p.sigma * signalNoise p * phi * deriv v phi + p.mu0 * v phi = 0)
    (hleft : ∀ phi, 0 < phi → phi ≤ A → v phi = 1 + phi)
    (hA : derivWithin v (Set.Icc A B) A = 1)
    (hB : derivWithin v (Set.Icc A B) B = 1 + eps) :
    A ≤ -p.mu0 / p.mu1 := by sorry

end DynkinAsymInfo.Linear
