-- Prove2me | Theorems.Thm_BosonicLearn_thermal_characteristic
-- name    : BosonicLearn.thermal_characteristic
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:42:33.855363+00:00
-- url     : https://prove2.me/theorems/523cd99b-5845-42be-83d6-f2584cd96316
-- title:
--   Characteristic function of a single-mode thermal state: $\sum_m d^m\langle m|D(z)|m\rangle=(1-d)^{-1}e^{-|z|^2(1+d)/(2(1-d))}$
-- statement:
--   The Weyl characteristic function of the single-mode thermal state $(1-d)\sum_md^m|m\rangle\langle m|$.
--
--   For $0\le d<1$ and $z\in\mathbb C$,
--
--   $$
--   \sum_{m=0}^\infty d^m\,\langle m|D(z)|m\rangle=\frac1{1-d}\exp\!\Big(-|z|^2\,\frac{1+d}{2(1-d)}\Big),
--   $$
--
--   and the series converges absolutely.
--
--   Role. For one mode, $\det(I-R)\Gamma(R)=(1-d)\sum_md^m|m\rangle\langle m|$ with $R=(d)$; this is its characteristic function, a Gaussian with variance $\tfrac12\frac{1+d}{1-d}$ per quadrature (mean photon number $d/(1-d)$). It is the single-mode input of `BosonicLearn.fugacity_characteristic`.
--
--   **Formalization Note** $\langle m|D(z)|m\rangle$ is `Dependency50.P39.displacementMatrix z m m` ($=e^{-|z|^2/2}L_m(|z|^2)$; the identity is the generating function of the Laguerre polynomials). The statement is a conjunction of `Summable` of the norms and `HasSum`; the value is the complex cast of a real number.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, Eqs. (2) and (4), pp. 4–5 (Gaussian states, characteristic function, passive Gaussian states); Lemma 2 and Eq. (21), p. 20 (passive Gaussian states as det(I − R)Γ(R))

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace BosonicLearn

/-- **Characteristic function of a single-mode thermal state.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, Eq. (2), pp. 4–5 (Gaussian states and their characteristic functions); Lemma 2, Eq. (21), p. 20 (for one mode,
`det(I − R)Γ(R) = (1 − d) ∑ₘ dᵐ |m⟩⟨m|`).

For `0 ≤ d < 1` and `z ∈ ℂ`, `∑ₘ dᵐ ⟨m|D(z)|m⟩ = (1 − d)⁻¹ exp(−|z|² (1 + d)/(2(1 − d)))`, with absolute
convergence.

**Formalization Note.** `⟨m|D(z)|m⟩` is `Dependency50.P39.displacementMatrix z m m` (`= e^{−|z|²/2} Lₘ(|z|²)`); the
identity is the generating function of the Laguerre polynomials. -/
theorem thermal_characteristic (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d < 1) (z : ℂ) :
    Summable (fun m : ℕ => ‖(d : ℂ) ^ m * displacementMatrix z m m‖) ∧
    HasSum (fun m : ℕ => (d : ℂ) ^ m * displacementMatrix z m m)
      (((1 - d)⁻¹ * Real.exp (-(Complex.normSq z) * (1 + d) / (2 * (1 - d))) : ℝ) : ℂ) := by sorry

end BosonicLearn
