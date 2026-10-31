-- Prove2me | Theorems.Thm_DuanCV_Gauss_lemma_1_standard_form_I
-- name    : DuanCV.Gauss.lemma_1_standard_form_I
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:03.352987+00:00
-- url     : https://prove2.me/theorems/cacb0c18-eb91-400b-ab5a-6306e89ff750
-- title:
--   Lemma 1 (standard form I)
-- statement:
--   Let $\rho$ be a two-mode Gaussian state with covariance matrix $V$ in the order $(\hat x_1,\hat p_1,\hat x_2,\hat p_2)$. There are $2\times2$ real symplectic matrices $S_1,S_2$ and reals $n,m\ge1$, $c,c'$ such that, with $S=S_1\oplus S_2$,
--
--   $$S^TVS=\begin{pmatrix} n&0&c&0\\ 0&n&0&c'\\ c&0&m&0\\ 0&c'&0&m\end{pmatrix}.$$
--
--   Local linear unitary Bogoliubov operations therefore reduce the ten entries of a covariance to four numbers.
--
--   Differences from the source:
--   - encoding: the correlation matrix M of Eq. (6), with linear terms removed by local displacements → the covariance V of GaussianWithCovariance: density operator, V ≻ 0, V + iJ ⪰ 0, finite mean energy, arbitrary first moments, and convergent Weyl traces equal to exp(−¼vᵀVv + i mᵀv); reason: v = √2 λ in Eqs. (5)–(6) gives M = V (vacuum V = I); the extra conditions hold for every Gaussian state, and first moments are kept rather than displaced away
--   - encoding: the state after LLUBOs U_l, whose correlation matrix changes by the congruence of Eq. (9) → the covariance SᵀVS and the quadratures (S w)·r̂ evaluated on the original ρ, with S = S₁ ⊕ S₂ symplectic; reason: this is the Heisenberg form the paper states on p. 3; the numbers are the same, and a 2 × 2 real matrix is symplectic exactly when its determinant is 1
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Lemma 1, Eq. (8), p. 3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov standardFormCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P08 (isSymplectic)
open QAlgorithms.Papers.Independent.Gap48.P47 (TwoModeGaussianDensity localCongruence)

namespace DuanCV.Gauss

/-- **Lemma 1 (standard form I).**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Lemma 1, Eq. (8), p. 3.

The covariance matrix of every two-mode Gaussian state is brought by local symplectic matrices to
the matrix (8), with `n, m ≥ 1`.

**Formalization Note.** LLUBOs act on the covariance by congruence (Heisenberg form, p. 3), so no
unitary appears. `standardFormCovariance n m c c'` has diagonal `(n, n, m, m)`, `c` at `(x̂₁, x̂₂)` and
`c'` at `(p̂₁, p̂₂)`. -/
theorem lemma_1_standard_form_I (ρ : TwoModeGaussianDensity) :
    ∃ S1 S2 : Cov 1, isSymplectic S1 ∧ isSymplectic S2 ∧
      ∃ n m c c' : ℝ, 1 ≤ n ∧ 1 ≤ m ∧
        localCongruence ρ.covariance S1 S2 = standardFormCovariance n m c c' := by sorry

end DuanCV.Gauss
