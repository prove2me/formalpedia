-- Prove2me | Theorems.Thm_DantzigSelector_Oracle_gaussian_max_tail
-- name    : DantzigSelector.Oracle.gaussian_max_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:49:59.480532+00:00
-- url     : https://prove2.me/theorems/1fbefaf6-a455-4f24-8498-42e399d471d8
-- title:
--   Section 3 — $P(\sup_j|\langle z,X_j\rangle|>u)\le 2p\,\varphi(u)/u$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have unit-normed columns $X_1,\dots,X_p$, $\|X_j\|_{\ell_2}=1$, and let $z=(z_1,\dots,z_n)$ be a vector of independent standard normal random variables on a probability space. Put $Z_j:=\langle z,X_j\rangle$, which is $N(0,1)$, and $\varphi(u):=(2\pi)^{-1/2}e^{-u^2/2}$. Then for every $u>0$,
--   $$P\Big(\sup_{1\le j\le p}|Z_j|>u\Big)\le 2p\cdot\frac{\varphi(u)}{u}.$$
--
--   With $u=\lambda_p$ this bounds the probability that the noise violates the orthogonality condition (3.1) $|\langle z,X_j\rangle|\le\lambda_p$ for all $j$; it is the only probabilistic input to Theorems 1.1 and 1.2.
--
--   **Formalization Note** Section 3 normalizes $\sigma=1$, so the noise coordinates have law $N(0,1)$ and are mutually independent. The event $\sup_j|Z_j|>u$ is written "some $j$ has $|Z_j|>u$", which is the same event since there are finitely many $j$; the probability is the measure of that set.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 15, Section 3 (sentence after Eq. (3.1))

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
import Definitions.Def_DantzigSelector_Oracle_Model

open MeasureTheory ProbabilityTheory CandesTao.Decoding DantzigSelector.Sparse

namespace DantzigSelector.Oracle

/-- Candès–Tao (2007), Section 3, p. 15 (σ = 1): if the columns of `X` are unit-normed and
`z_1, …, z_n` are independent `N(0,1)` variables, then `Z_j := ⟨z, X_j⟩` obeys, for every
`u > 0`, `P(sup_j |Z_j| > u) ≤ 2p · φ(u)/u` with `φ(u) = (2π)^{-1/2} e^{-u²/2}`. -/
theorem gaussian_max_tail {n p : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitNormColumns X)
    (z : Fin n → Ω → ℝ) (hz : ∀ i, HasLaw (z i) (gaussianReal 0 1) P) (hind : iIndepFun z P)
    (u : ℝ) (hu : 0 < u) :
    P {ω | ∃ j : Fin p, u < |∑ i, X i j * z i ω|} ≤
      ENNReal.ofReal
        (2 * (p : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-u ^ 2 / 2)) / u) := by sorry

end DantzigSelector.Oracle
