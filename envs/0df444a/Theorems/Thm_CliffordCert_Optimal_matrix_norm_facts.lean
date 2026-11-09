-- Prove2me | Theorems.Thm_CliffordCert_Optimal_matrix_norm_facts
-- name    : CliffordCert.Optimal.matrix_norm_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:48:21.189726+00:00
-- url     : https://prove2.me/theorems/854b33ba-dc90-4193-8d00-90309a2b760f
-- title:
--   Fact 1 — matrix norms, attained duality and positivity
-- statement:
--   For a Hermitian matrix $X$ of positive size $d$, the trace norm, Hilbert–Schmidt norm and Euclidean operator norm satisfy
--   $$\|X\|_1\le\sqrt d\|X\|_2,\qquad\|X\|_2^2\le\|X\|_\infty\|X\|_1,\qquad\|X\|_1=\max_{S=S^\dagger,\,-I\preceq S\preceq I}\operatorname{Tr}(SX).$$
--   The maximum is attained. For positive semidefinite $A,B$, $\operatorname{Tr}(AB)\ge0$. For $T\succeq0$ and Hermitian $Y$,
--   $$\operatorname{Tr}(T^{1/2}YT^{1/2}Y)\le\operatorname{Tr}(TY^2).$$
--   Every complex-linear positive trace-preserving map to any finite matrix size contracts the trace norm of Hermitian inputs.
--
--   These are all clauses of Fact 1, including the attained maximum and positivity statements used in the estimator analysis.
--
--   Differences from the source:
--   - encoding: the maximum over Hermitian contractions → a maximizing Hermitian witness and an upper bound for every admissible witness; reason: this retains attainment and avoids a default-valued supremum
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 9, Fact 1, Eqs. (11)–(13) (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_spectral_protocol
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem matrix_norm_facts (d : ℕ) (hd : 1 ≤ d) :
    (∀ X : Mat (Fin d), X.IsHermitian →
      WildeQIT.traceNorm X ≤ Real.sqrt (d : ℝ) * hsNorm X ∧
      hsSq X ≤ opNorm X * WildeQIT.traceNorm X) ∧
    (∀ X : Mat (Fin d), X.IsHermitian →
      (∃ S : Mat (Fin d), S.IsHermitian ∧ (1+S).PosSemidef ∧ (1-S).PosSemidef ∧
        born S X = WildeQIT.traceNorm X) ∧
      (∀ S : Mat (Fin d), S.IsHermitian → (1+S).PosSemidef → (1-S).PosSemidef →
        born S X ≤ WildeQIT.traceNorm X)) ∧
    (∀ A B : Mat (Fin d), A.PosSemidef → B.PosSemidef → 0 ≤ born A B) ∧
    (∀ T Y : Mat (Fin d), T.PosSemidef → Y.IsHermitian →
      (Matrix.trace (CFC.sqrt T * Y * CFC.sqrt T * Y)).re ≤
        (Matrix.trace (T * Y^2)).re) ∧
    (∀ (r : ℕ) (Φ : Mat (Fin d) →ₗ[ℂ] Mat (Fin r)),
      (∀ A, A.PosSemidef → (Φ A).PosSemidef) →
      (∀ A, Matrix.trace (Φ A) = Matrix.trace A) →
      ∀ X : Mat (Fin d), X.IsHermitian →
        WildeQIT.traceNorm (Φ X) ≤ WildeQIT.traceNorm X) := by sorry
end CliffordCert.Optimal
