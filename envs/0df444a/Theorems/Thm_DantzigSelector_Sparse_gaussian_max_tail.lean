-- Prove2me | Theorems.Thm_DantzigSelector_Sparse_gaussian_max_tail
-- name    : DantzigSelector.Sparse.gaussian_max_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:41:42.286804+00:00
-- url     : https://prove2.me/theorems/599f3ff0-daf2-4f6c-80e6-c5025dde990e
-- title:
--   Section 3: $P(\sup_j|Z_j|>u)\le2p\,\varphi(u)/u$ for $Z_j=\langle z,X_j\rangle$
-- statement:
--   Let $z=(z_1,\dots,z_n)$ be a vector of independent standard normal random variables on a probability space, and let $X\in\mathbb R^{n\times p}$ have unit-normed columns $X_1,\dots,X_p$. Put $Z_j:=\langle z,X_j\rangle$, so that each $Z_j\sim N(0,1)$. Then for every $u>0$,
--   $$
--   \mathbb P\Bigl(\sup_{1\le j\le p}|Z_j|>u\Bigr)\le2p\cdot\frac{\varphi(u)}{u},\qquad\varphi(u):=(2\pi)^{-1/2}e^{-u^2/2}.
--   $$
--
--   This is the only probabilistic input of Theorem 1.1: with $u=\lambda_p=\sqrt{2(1+a)\log p}$ it shows that the orthogonality condition (3.1) fails with probability at most $(\sqrt{\pi(1+a)\log p}\cdot p^a)^{-1}$.
--
--   **Formalization Note** The noise is a family `z : Fin n → Ω → ℝ` of mutually independent random variables, each with law `gaussianReal 0 1`. The event $\{\sup_j|Z_j|>u\}$ is written as $\{\exists j,\ u<|Z_j|\}$, and its probability is bounded in $[0,\infty]$ by `ENNReal.ofReal` of the right-hand side.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 15, Section 3 ("for each u > 0, P(sup_j |Z_j| > u) ≤ 2p·φ(u)/u")

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
open CandesTao.Decoding
open MeasureTheory ProbabilityTheory

namespace DantzigSelector.Sparse

/-- Section 3, p. 15: if `z_1, …, z_n` are independent standard normal random variables and the
columns of `X` are unit-normed, then with `Z_j := ⟨z, X_j⟩`, for every `u > 0`,
`P(sup_j |Z_j| > u) ≤ 2p · φ(u)/u`, where `φ(u) = (2π)^{-1/2} e^{-u²/2}`. -/
theorem gaussian_max_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitNormColumns X)
    (z : Fin n → Ω → ℝ) (hz : ∀ i, HasLaw (z i) (gaussianReal 0 1) P) (hind : iIndepFun z P)
    (u : ℝ) (hu : 0 < u) :
    P {ω | ∃ j : Fin p, u < |∑ i, X i j * z i ω|} ≤
      ENNReal.ofReal (2 * p * (Real.exp (-u ^ 2 / 2) / Real.sqrt (2 * Real.pi)) / u) := by sorry

end DantzigSelector.Sparse
