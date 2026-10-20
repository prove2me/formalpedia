-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_lemma_6_7
-- name    : DynkinAsymInfo.Linear.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:34.995994+00:00
-- url     : https://prove2.me/theorems/dbd97af1-331c-407f-86c5-8dfe2ba7242c
-- title:
--   Lemma 6.7 — scaled value exceeds immediate stopping
-- statement:
--   Let $0<A<B$, $\mu_0<0<\mu_1$, and $\varepsilon>0$. If $V$ is $C^2$ on $[A,B]$ and solves the Euler ODE and all three boundary conditions in (85), then
--   $$V(\phi)>1+\phi,\qquad V'(\phi)>1\qquad(A<\phi<B).$$
--   This strict inequality identifies the interior continuation region of the uninformed player. Endpoint derivatives in (85) are one-sided.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, p. 22, Lemma 6.7, (85)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_Model

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, p. 22, Lemma 6.7,
with the full boundary-value problem (85), p. 22. -/
theorem lemma_6_7 (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (eps : ℝ) (heps : 0 < eps) (A B : ℝ) (hAB : 0 < A ∧ A < B)
    (v : ℝ → ℝ) (hC2 : ContDiffOn ℝ 2 v (Set.Icc A B))
    (hODE : ∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv v) phi +
      p.sigma * signalNoise p * phi * deriv v phi + p.mu0 * v phi = 0)
    (hleft : ∀ phi, 0 < phi → phi ≤ A → v phi = 1 + phi)
    (hA : derivWithin v (Set.Icc A B) A = 1)
    (hB : derivWithin v (Set.Icc A B) B = 1 + eps) :
    ∀ phi ∈ Set.Ioo A B, 1 + phi < v phi ∧ 1 < deriv v phi := by sorry

end DynkinAsymInfo.Linear
