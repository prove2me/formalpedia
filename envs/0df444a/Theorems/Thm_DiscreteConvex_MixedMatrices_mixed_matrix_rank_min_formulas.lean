-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_mixed_matrix_rank_min_formulas
-- name    : DiscreteConvex.MixedMatrices.mixed_matrix_rank_min_formulas
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T06:47:57.408465+00:00
-- url     : https://prove2.me/theorems/95b711f1-45da-4f94-b0bc-4581c7007d3c
-- title:
--   Theorem 12.8 -- three dual min-formulas for the rank
-- statement:
--   **Theorem 12.8** (p.358, Eqs. (12.10)-(12.12)). For a mixed matrix $A = Q + T$, writing $\rho(I,J) = \operatorname{rank} Q[I,J]$, $\tau(I,J) = \operatorname{rank} T[I,J]$, and $\gamma(I,J)$ for the number of nonzero rows of $T[I,J]$:
--   $$\operatorname{rank} A = \min_{I \subseteq R,\, J \subseteq C}\{\rho(I,J) + \tau(I,J) - |I| - |J|\} + |R| + |C|,$$
--   $$\operatorname{rank} A = \min_{I \subseteq R,\, J \subseteq C}\{\rho(I,J) + \gamma(I,J) - |I| - |J|\} + |R| + |C|,$$
--   $$\operatorname{rank} A = \min_{I \subseteq R,\, J \subseteq C,\ \gamma(I,J)=0}\{\rho(I,J) - |I| - |J|\} + |R| + |C|.$$
--   These are three genuinely distinct formulas (not restatements of one another): the first converts Theorem 12.7's max-formula via Edmonds's matroid intersection theorem, the second substitutes a min-max relation for maximum matchings in place of $\tau$, and the third restricts to the pairs where $T[I,J]$ vanishes entirely. Each is evaluable efficiently ($\rho$ by Gaussian elimination, $\tau$ and $\gamma$ by bipartite matching), which is what makes computing $\operatorname{rank} A$ tractable despite Theorem 12.7's exponential-size maximization.
--
--   **Formalization Note.** The third formula's restricted minimum is formalized over `WithTop ℤ`, with pairs violating $\gamma(I,J)=0$ contributing $+\infty$ to a `Finset.inf` over *all* pairs, rather than via an explicit filtered-Finset minimum — an equivalent, faithful rendering of the same restricted minimum that elaborates far more efficiently in Lean.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.358, Theorem 12.8.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.358, Theorem 12.8

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank
import Definitions.Def_DiscreteConvex_MixedMatrices_GammaFun

namespace DiscreteConvex.MixedMatrices

/-- Theorem 12.8 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.358), Eqs. (12.10)-(12.12).
For a mixed matrix `A = Q + T`, three equal min-formulas for `rank A`, in terms of `ρ(I,J) = rank
Q[I,J]`, `τ(I,J) = rank T[I,J]`, and `γ(I,J)`, the number of nonzero rows of `T[I,J]`. The third
formula's minimum is restricted to pairs `(I,J)` with `γ(I,J) = 0`; formalized over `WithTop ℤ`,
with excluded pairs contributing `⊤` to the `Finset.inf`, rather than via `Finset.filter` +
`Finset.inf'` (an equivalent but computationally much cheaper-to-elaborate rendering of the same
restricted minimum). -/
theorem mixed_matrix_rank_min_formulas {R C K F : Type*} [Fintype R] [Fintype C] [Field K]
    [Field F] [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T) :
    ((A.rank : ℤ) =
        (Finset.univ : Finset (Finset R × Finset C)).inf' Finset.univ_nonempty
          (fun p => (MatrixSubRank Q p.1 p.2 : ℤ) + (MatrixSubRank T p.1 p.2 : ℤ) -
            p.1.card - p.2.card) +
          Fintype.card R + Fintype.card C) ∧
      ((A.rank : ℤ) =
        (Finset.univ : Finset (Finset R × Finset C)).inf' Finset.univ_nonempty
          (fun p => (MatrixSubRank Q p.1 p.2 : ℤ) + (GammaFun T p.1 p.2 : ℤ) -
            p.1.card - p.2.card) +
          Fintype.card R + Fintype.card C) ∧
      ((A.rank : WithTop ℤ) =
        (Finset.univ : Finset (Finset R × Finset C)).inf
            (fun p => if GammaFun T p.1 p.2 = 0
                      then ((MatrixSubRank Q p.1 p.2 : ℤ) - p.1.card - p.2.card : WithTop ℤ)
                      else ⊤) +
          (Fintype.card R : WithTop ℤ) + (Fintype.card C : WithTop ℤ)) := by sorry

end DiscreteConvex.MixedMatrices
