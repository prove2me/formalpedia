-- Prove2me | Theorems.Thm_BosonicLearn_traceDist_triangle
-- name    : BosonicLearn.traceDist_triangle
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T06:53:45.652093+00:00
-- url     : https://prove2.me/theorems/407084ba-525f-44de-9a6e-4806a26994f2
-- title:
--   Triangle inequality for the trace distance: $\tfrac12\|A-C\|_1\le\tfrac12\|A-B\|_1+\tfrac12\|B-C\|_1$
-- statement:
--   The trace distance satisfies the triangle inequality.
--
--   Let $I$ be an index set and $A,B,C$ coefficient arrays on $I\times I$. With the trace norm $\|X\|_1\in[0,\infty]$ defined as the infimum of $\sum_k\|\ell_k\|\,\|r_k\|$ over nuclear expansions $X_{ij}=\sum_k\ell_k(i)\overline{r_k(j)}$, $\ell_k,r_k\in\ell^2(I)$ (and $\infty$ if $X$ is not trace class),
--
--   $$
--   \tfrac12\|A-C\|_1\;\le\;\tfrac12\|A-B\|_1+\tfrac12\|B-C\|_1 .
--   $$
--
--   Role. In the proof of Theorem 8 the error of the estimate $\hat\rho=\rho(\hat\mu,\tilde\Sigma)$ is split through the intermediate state $\rho(\hat\mu,\Sigma)$ into a covariance part (Theorem 7) and a first-moment part (Lemma 18).
--
--   **Formalization Note** `traceDist A B = traceSize (A − B) / 2` with values in `ℝ≥0∞`. No positivity or normalization of the arrays is assumed.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) and `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Eq. (218), p. 62 (triangle inequality through the intermediate state ρ(µ̂, Σ) in the proof of Theorem 8)

import Mathlib
import Definitions.Def_BosonicLearn_traceDist

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open scoped ENNReal

namespace BosonicLearn

/-- **Triangle inequality for the trace distance.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §7.2, proof of Theorem 8, Eq. (218), p. 62: "Inserting the intermediate state ρ(µ̂, Σ) and using the
triangle inequality, we find ½‖ρ̂ − ρ(µ, Σ)‖₁ ≤ ½‖ρ(µ̂, Σ̃) − ρ(µ̂, Σ)‖₁ + ½‖ρ(µ̂, Σ) − ρ(µ, Σ)‖₁."

For coefficient arrays `A, B, C` on any index set, `½‖A − C‖₁ ≤ ½‖A − B‖₁ + ½‖B − C‖₁`.

**Formalization Note.** `traceDist A B = traceSize (A − B) / 2` with values in `[0, ∞]`; the trace norm is the
infimum over nuclear expansions, and is `∞` for arrays that are not trace class, so the inequality holds for
all arrays. -/
theorem traceDist_triangle {I : Type} (A B C : Matrix I I ℂ) :
    traceDist A C ≤ traceDist A B + traceDist B C := by sorry

end BosonicLearn
