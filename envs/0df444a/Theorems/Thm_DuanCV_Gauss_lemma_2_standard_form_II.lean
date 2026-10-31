-- Prove2me | Theorems.Thm_DuanCV_Gauss_lemma_2_standard_form_II
-- name    : DuanCV.Gauss.lemma_2_standard_form_II
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:35.334185+00:00
-- url     : https://prove2.me/theorems/23fe9301-0150-4aff-9b08-fe45311574c5
-- title:
--   Lemma 2 (standard form II) (corrected: (11a) cross-multiplied)
-- statement:
--   Let $\rho$ be a two-mode Gaussian state with covariance matrix $V$. There are $2\times2$ real symplectic matrices $S_1,S_2$ and reals $n_i,m_i,c_i$ such that, with $S=S_1\oplus S_2$,
--
--   $$S^TVS=\begin{pmatrix} n_1&0&c_1&0\\ 0&n_2&0&c_2\\ c_1&0&m_1&0\\ 0&c_2&0&m_2\end{pmatrix},$$
--
--   where $(n_1-1)(m_2-1)=(n_2-1)(m_1-1)$ and
--
--   $$|c_1|-|c_2|=\sqrt{(n_1-1)(m_1-1)}-\sqrt{(n_2-1)(m_2-1)},$$
--
--   both radicands being nonnegative.
--
--   This is the form in which the inequality of Theorem 1 becomes sharp for Gaussian states.
--
--   Differences from the source:
--   - correction: (11a): (n₁−1)/(m₁−1) = (n₂−1)/(m₂−1) → (n₁−1)(m₂−1) = (n₂−1)(m₁−1); reason: the ratio is undefined for ρ_th(n̄) ⊗ |0⟩⟨0| with n̄ > 0: mode 2 is pure, so every rendering has m₁m₂ = 1 and c₁ = c₂ = 0, and (11) then forces m₁ = m₂ = 1, i.e. 0/0
--   - encoding: the real square roots of (11b) → the radicands (nᵢ−1)(mᵢ−1) are required to be nonnegative; reason: the printed square roots presuppose this; Lean's Real.sqrt is 0 on negative numbers, so it is written out
--   - encoding: the correlation matrix M of Eq. (6), with linear terms removed by local displacements → the covariance V of GaussianWithCovariance: density operator, V ≻ 0, V + iJ ⪰ 0, finite mean energy, arbitrary first moments, and convergent Weyl traces equal to exp(−¼vᵀVv + i mᵀv); reason: v = √2 λ in Eqs. (5)–(6) gives M = V (vacuum V = I); the extra conditions hold for every Gaussian state, and first moments are kept rather than displaced away
--   - encoding: the state after LLUBOs U_l, whose correlation matrix changes by the congruence of Eq. (9) → the covariance SᵀVS and the quadratures (S w)·r̂ evaluated on the original ρ, with S = S₁ ⊕ S₂ symplectic; reason: this is the Heisenberg form the paper states on p. 3; the numbers are the same, and a 2 × 2 real matrix is symplectic exactly when its determinant is 1
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Lemma 2, Eqs. (10)–(11), pp. 3–4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47
import Definitions.Def_DuanCV_Gauss_IsFormII

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)
open QAlgorithms.Papers.Independent.Frontier30.P08 (isSymplectic)
open QAlgorithms.Papers.Independent.Gap48.P47 (TwoModeGaussianDensity localCongruence)

namespace DuanCV.Gauss

/-- **Lemma 2 (standard form II), with (11a) cross-multiplied.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Lemma 2, Eqs. (10)–(11), pp. 3–4.

The covariance matrix of every two-mode Gaussian state is brought by local symplectic matrices to
the matrix (10), with parameters satisfying (11).

**Formalization Note.** `IsFormII` carries (11a) in cross-multiplied form. The printed ratio is `0/0`
for every rendering of `ρ_th ⊗ |0⟩⟨0|` with mean photon number `n̄ > 0`. -/
theorem lemma_2_standard_form_II (ρ : TwoModeGaussianDensity) :
    ∃ S1 S2 : Cov 1, isSymplectic S1 ∧ isSymplectic S2 ∧
      ∃ n1 n2 m1 m2 c1 c2 : ℝ,
        IsFormII (localCongruence ρ.covariance S1 S2) n1 n2 m1 m2 c1 c2 := by sorry

end DuanCV.Gauss
