-- Prove2me | Theorems.Thm_DuanCV_Gauss_gaussian_separable_iff_epr_total_variance
-- name    : DuanCV.Gauss.gaussian_separable_iff_epr_total_variance
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:58:01.275841+00:00
-- url     : https://prove2.me/theorems/9933505f-5509-4f86-bb16-31e689979759
-- title:
--   Theorem 2 — a two-mode Gaussian state is separable iff, in standard form II, $\langle(\Delta\hat u)^2\rangle+\langle(\Delta\hat v)^2\rangle\ge a_0^2+1/a_0^2$ (corrected: (11a) cross-multiplied)
-- statement:
--   Let $\rho$ range over two-mode Gaussian states, with covariance matrix $V$ and arbitrary first moments.
--
--   1. Every such $\rho$ has a standard form II: there are $2\times2$ real symplectic matrices $S_1,S_2$ and reals $n_i,m_i,c_i$ such that, with $S=S_1\oplus S_2$, the matrix $S^TVS$ is $M_s^{II}$ with parameters satisfying Eq. (11).
--   2. Let $S_1,S_2$ be symplectic and let $S^TVS$ be $M_s^{II}$ with parameters $n_i,m_i,c_i$ satisfying Eq. (11). Let $a_0>0$ with $a_0^4(n_i-1)=m_i-1$ for $i=1,2$, that is, $a_0^2=\sqrt{(m_i-1)/(n_i-1)}$, and let $\varepsilon_i=\pm1$ with $\varepsilon_ic_i=|c_i|$. Let
--
--   $$\hat u=a_0\hat x_1-\frac{\varepsilon_1}{a_0}\hat x_2,\qquad \hat v=a_0\hat p_1-\frac{\varepsilon_2}{a_0}\hat p_2$$
--
--   be the operators of the transformed frame, that is, $(Sw)\cdot\hat r$ for their coefficient vectors $w$. Then
--
--   $$\rho\text{ is separable}\quad\Longleftrightarrow\quad \bigl\langle(\Delta\hat u)^2\bigr\rangle_\rho+\bigl\langle(\Delta\hat v)^2\bigr\rangle_\rho\ \ge\ a_0^2+\frac1{a_0^2}.$$
--
--   This is the paper's main theorem: for Gaussian states, one inequality on the total variance of a single pair of EPR-type operators decides separability.
--
--   Differences from the source:
--   - generalization: the state 'expressed in its standard form II', i.e. the rendering Lemma 2 produces → every local symplectic rendering with (10)–(11), including renderings with some nᵢ < 1, together with clause 1 that a rendering exists; reason: the paper's rendering is one instance, so the 'for every' form specializes to the source, and clause 1 is the theorem's 'its standard form II'
--   - correction: (11a): (n₁−1)/(m₁−1) = (n₂−1)/(m₂−1) → (n₁−1)(m₂−1) = (n₂−1)(m₁−1); reason: the ratio is undefined for ρ_th(n̄) ⊗ |0⟩⟨0| with n̄ > 0: mode 2 is pure, so every rendering has m₁m₂ = 1 and c₁ = c₂ = 0, and (11) then forces m₁ = m₂ = 1, i.e. 0/0
--   - encoding: the real square roots of (11b) → the radicands (nᵢ−1)(mᵢ−1) are required to be nonnegative; reason: the printed square roots presuppose this; Lean's Real.sqrt is 0 on negative numbers, so it is written out
--   - reading: Eq. (1): ρ = ∑ᵢ pᵢ ρᵢ₁ ⊗ ρᵢ₂ with the index range left open → ρ lies in the trace-norm closed convex hull of product states (Holevo–Shirokov–Werner); reason: the paper's own proof of Theorem 2 concludes separability from the continuous mixture (19), and the closed hull contains every finite, countable and integral mixture of product states
--   - encoding: ⟨(Δû)²⟩_ρ for a quadrature û = w·r̂ → the variance in ℝ≥0∞ of the unique probability law on ℝ whose characteristic function is the Weyl trace tr ρ exp(i t w·r̂); reason: this is the variance of the observable; the value is ⊤ when the second moment is infinite, a case the paper does not discuss and in which (3) holds trivially
--   - encoding: the state after LLUBOs U_l, whose correlation matrix changes by the congruence of Eq. (9) → the covariance SᵀVS and the quadratures (S w)·r̂ evaluated on the original ρ, with S = S₁ ⊕ S₂ symplectic; reason: this is the Heisenberg form the paper states on p. 3; the numbers are the same, and a 2 × 2 real matrix is symplectic exactly when its determinant is 1
--   - encoding: the correlation matrix M of Eq. (6), with linear terms removed by local displacements → the covariance V of GaussianWithCovariance: density operator, V ≻ 0, V + iJ ⪰ 0, finite mean energy, arbitrary first moments, and convergent Weyl traces equal to exp(−¼vᵀVv + i mᵀv); reason: v = √2 λ in Eqs. (5)–(6) gives M = V (vacuum V = I); the extra conditions hold for every Gaussian state, and first moments are kept rather than displaced away
--   - encoding: a₀² = √((m₁−1)/(n₁−1)) = √((m₂−1)/(n₂−1)) → 0 < a₀, a₀⁴(n₁−1) = m₁−1, a₀⁴(n₂−1) = m₂−1; reason: this is the paper's value wherever it is defined, written without Lean division; it excludes only the states where no positive a₀ exists (such as ρ_th ⊗ |0⟩⟨0|), for which the printed formula gives a₀ = 0
--   - generalization: a₀ defined by ratios, which are 0/0 when nᵢ = mᵢ = 1 for some i → the equation a₀⁴(nᵢ−1) = mᵢ−1 holds for every a₀ when nᵢ = mᵢ = 1, so those renderings are included; reason: the printed theorem says nothing at 0/0; where the ratios are defined this is the paper's a₀
--   - encoding: the sign c/|c| in Eq. (15) → any ε = ±1 with ε c = |c|; reason: at c = 0 the printed quotient is undefined, and both signs give the same variance
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Theorem 2, Eqs. (15a)–(15b), p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47
import Definitions.Def_DuanCV_Gauss_IsSeparableTwoMode
import Definitions.Def_DuanCV_Gauss_quadVariance
import Definitions.Def_DuanCV_Gauss_eprU
import Definitions.Def_DuanCV_Gauss_eprV
import Definitions.Def_DuanCV_Gauss_IsFormII

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)
open QAlgorithms.Papers.Independent.Frontier30.P08 (isSymplectic)
open QAlgorithms.Papers.Independent.Gap48.P47 (TwoModeGaussianDensity localCongruence localSymplecticMatrix)

namespace DuanCV.Gauss

/-- **Theorem 2 (necessary and sufficient inseparability criterion for Gaussian states).**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Theorem 2, Eqs. (15), p. 4.

Clause 1: every two-mode Gaussian state has a standard form II (the "its standard form II" of the
theorem). Clause 2: for every rendering of the state in standard form II, every admissible `a₀` and
the signs `εᵢ` of `cᵢ`, the state is separable if and only if the operators (15) satisfy (3).

**Formalization Note.** `S = localSymplecticMatrix S1 S2`, and the quadrature `w·r̂'` of the transformed
frame is `(S.mulVec w)·r̂` on `ρ`, with covariance `SᵀVS`. `a₀² = √((m₁-1)/(n₁-1)) = √((m₂-1)/(n₂-1))`
is encoded as `0 < a₀`, `a₀⁴(n₁-1) = m₁-1`, `a₀⁴(n₂-1) = m₂-1`, and `c/|c|` as a sign `ε` with
`ε c = |c|` (at `c = 0` both signs give the same variance). There is no Lean division in a hypothesis.

Proof note (not part of the statement): if some `nᵢ < 1`, the inequality forces the matching
`cᵢ = 0`, and a further local squeeze reaches `SᵀVS ⪰ I` by physicality. -/
theorem gaussian_separable_iff_epr_total_variance :
    (∀ ρ : TwoModeGaussianDensity,
      ∃ S1 S2 : Cov 1, isSymplectic S1 ∧ isSymplectic S2 ∧
        ∃ n1 n2 m1 m2 c1 c2 : ℝ,
          IsFormII (localCongruence ρ.covariance S1 S2) n1 n2 m1 m2 c1 c2) ∧
    (∀ (ρ : TwoModeGaussianDensity) (S1 S2 : Cov 1),
      isSymplectic S1 → isSymplectic S2 →
      ∀ n1 n2 m1 m2 c1 c2 : ℝ,
        IsFormII (localCongruence ρ.covariance S1 S2) n1 n2 m1 m2 c1 c2 →
      ∀ a0 ε1 ε2 : ℝ, 0 < a0 → a0 ^ 4 * (n1 - 1) = m1 - 1 → a0 ^ 4 * (n2 - 1) = m2 - 1 →
        (ε1 = 1 ∨ ε1 = -1) → ε1 * c1 = |c1| →
        (ε2 = 1 ∨ ε2 = -1) → ε2 * c2 = |c2| →
        (IsSeparableTwoMode ρ.density.coefficients ↔
          ENNReal.ofReal (a0 ^ 2 + 1 / a0 ^ 2) ≤
            quadVariance ρ.density.coefficients
                ((localSymplecticMatrix S1 S2).mulVec (eprU a0 (-ε1))) +
              quadVariance ρ.density.coefficients
                ((localSymplecticMatrix S1 S2).mulVec (eprV a0 (-ε2))))) := by sorry

end DuanCV.Gauss
