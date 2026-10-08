-- Prove2me | Theorems.Thm_AMPUniversality_Polytope_lemma_5
-- name    : AMPUniversality.Polytope.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:45.698454+00:00
-- url     : https://prove2.me/theorems/397672da-9a8e-43da-9d48-c16f6f1be5cd
-- title:
--   Lemma 5, p. 41 — approximate dual certificate implies unique ℓ¹ recovery
-- statement:
--   For every $c_1,c_2,c_3>0$ there is a tolerance $\varepsilon_0>0$ such that a signal $x_0$ is uniquely recovered by minimizing $\|x\|_1$ subject to $Ax=Ax_0$ when three conditions hold: an $\ell^1$ subgradient $v$ has a representation $v=A^Tz+w$ with $\|w\|_2\leq\sqrt n\,\varepsilon$ and $\varepsilon\leq\varepsilon_0$; every submatrix on $S(c_1)\cup S'$ for $|S'|\leq c_1n$ has least singular value at least $c_2$; and $c_3^{-1}\leq\sigma_{\max}(A)^2\leq c_3$.
--
--   $$Ax=Ax_0,\quad x\ne x_0\quad\Longrightarrow\quad\|x_0\|_1<\|x\|_1.$$
--
--   The lemma converts a nearly valid dual certificate and uniform spectral control into exact recovery. **Formalization Note** All vector norms here are Euclidean except the optimization objective, which is the sum of coordinate absolute values. The restricted least singular value is its action on unit column vectors, as required by the lemma's proof.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 41, Lemma 5

import Mathlib
import Definitions.Def_AMPUniversality_Polytope_Recovery
import Definitions.Def_AMPUniversality_Polytope_Certificate

set_option autoImplicit false
open Set
open scoped BigOperators

namespace AMPUniversality.Polytope

/-- Lemma 5, p. 41: an approximate dual certificate and uniform restricted
singular-value bounds imply unique basis-pursuit recovery. -/
theorem lemma_5 :
    ∀ c1 c2 c3 : ℝ, 0 < c1 → 0 < c2 → 0 < c3 →
      ∃ ε0 : ℝ, 0 < ε0 ∧
        ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
          (x0 : Fin n → ℝ) (ε : ℝ),
          ε ≤ ε0 →
          (∃ (v w : Fin n → ℝ) (z : Fin m → ℝ),
            IsL1Subgradient x0 v ∧
            v = Matrix.mulVec A.transpose z + w ∧
            Real.sqrt (euclideanNormSq w) ≤ Real.sqrt (n : ℝ) * ε ∧
            (∀ S' : Finset (Fin n),
              (S'.card : ℝ) ≤ c1 * (n : ℝ) →
              (↑c2 : WithTop ℝ) ≤
                sigmaMin A (nearSaturation v c1 ∪ S')) ∧
            c3⁻¹ ≤ sigmaMaxSq A ∧ sigmaMaxSq A ≤ c3) →
          L1Succeeds A x0 := by sorry

end AMPUniversality.Polytope
