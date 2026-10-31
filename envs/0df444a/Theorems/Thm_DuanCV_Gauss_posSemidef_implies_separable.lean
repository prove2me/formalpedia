-- Prove2me | Theorems.Thm_DuanCV_Gauss_posSemidef_implies_separable
-- name    : DuanCV.Gauss.posSemidef_implies_separable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:53.72353+00:00
-- url     : https://prove2.me/theorems/2219b68d-92c4-4d1d-bc15-ec36bf132801
-- title:
--   Eqs. (18)–(19) — $S^TVS\succeq I$ gives a positive P-representation, so the state is separable
-- statement:
--   Let $\rho$ be a two-mode Gaussian state with covariance matrix $V$ and arbitrary first moments. If there are $2\times2$ real symplectic matrices $S_1,S_2$ such that, with $S=S_1\oplus S_2$,
--
--   $$S^TVS-I\ \succeq\ 0,$$
--
--   then $\rho$ is separable.
--
--   In the frame given by $S$ the normally ordered characteristic function is Gaussian with the positive semi-definite matrix $S^TVS-I$, so the state is a mixture of product coherent states with a positive Gaussian weight, possibly singular. Separability is unchanged by the local operation that passes to this frame.
--
--   Differences from the source:
--   - reading: Eq. (1): ρ = ∑ᵢ pᵢ ρᵢ₁ ⊗ ρᵢ₂ with the index range left open → ρ lies in the trace-norm closed convex hull of product states (Holevo–Shirokov–Werner); reason: the paper's own proof of Theorem 2 concludes separability from the continuous mixture (19), and the closed hull contains every finite, countable and integral mixture of product states
--   - encoding: the correlation matrix M of Eq. (6), with linear terms removed by local displacements → the covariance V of GaussianWithCovariance: density operator, V ≻ 0, V + iJ ⪰ 0, finite mean energy, arbitrary first moments, and convergent Weyl traces equal to exp(−¼vᵀVv + i mᵀv); reason: v = √2 λ in Eqs. (5)–(6) gives M = V (vacuum V = I); the extra conditions hold for every Gaussian state, and first moments are kept rather than displaced away
--   - encoding: the state after LLUBOs U_l, whose correlation matrix changes by the congruence of Eq. (9) → the covariance SᵀVS and the quadratures (S w)·r̂ evaluated on the original ρ, with S = S₁ ⊕ S₂ symplectic; reason: this is the Heisenberg form the paper states on p. 3; the numbers are the same, and a 2 × 2 real matrix is symplectic exactly when its determinant is 1
--   - generalization: Ms^II − I ⪰ 0 for the standard form II covariance, with the remark that LLUBOs preserve separability → SᵀVS − I ⪰ 0 for any local symplectic S; reason: the source's matrix is the instance S = the rendering of Lemma 2; the general form is what the goal needs in the branch with some nᵢ < 1
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Eqs. (18)–(19), pp. 4–5, with the remark on LLUBOs, p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47
import Definitions.Def_DuanCV_Gauss_IsSeparableTwoMode

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)
open QAlgorithms.Papers.Independent.Frontier30.P08 (isSymplectic)
open QAlgorithms.Papers.Independent.Gap48.P47 (TwoModeGaussianDensity localCongruence)

namespace DuanCV.Gauss

/-- **A local symplectic image of the covariance above `I` gives a separable state.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Eqs. (18)–(19), pp. 4–5, with the remark on LLUBOs on p. 4.

If some local symplectic `S1, S2` make `SᵀVS - I` positive semi-definite, the state has a positive
Gaussian P-function in the transformed frame, i.e. it is a mixture of product coherent states, so
it is separable.

**Formalization Note.** First moments are arbitrary, and `SᵀVS - I` may be singular, in which case
the mixing measure is a singular Gaussian. -/
theorem posSemidef_implies_separable (ρ : TwoModeGaussianDensity)
    (h : ∃ S1 S2 : Cov 1, isSymplectic S1 ∧ isSymplectic S2 ∧
      (localCongruence ρ.covariance S1 S2 - 1).PosSemidef) :
    IsSeparableTwoMode ρ.density.coefficients := by sorry

end DuanCV.Gauss
