-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_mixed_matrix_nonsingular_iff
-- name    : DiscreteConvex.MixedMatrices.mixed_matrix_nonsingular_iff
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T06:57:30.995971+00:00
-- url     : https://prove2.me/theorems/810dfa18-a888-4115-a4ee-2264b34c64e7
-- title:
--   Proposition 12.6 -- nonsingularity of a mixed matrix
-- statement:
--   **Proposition 12.6** (p.357). A square mixed matrix $A = Q + T$ is nonsingular if and only if there exist $I \subseteq R$ and $J \subseteq C$ such that both $Q[I,J]$ and $T[R\setminus I, C\setminus J]$ are nonsingular.
--
--   This is the combinatorial certificate underlying every later result of the chapter: it reduces the (numerically delicate) nonsingularity of a matrix mixing exact and generic entries to a combinatorial search over row/column splits, each half checked in its own, easier arithmetic (numeric determinant for $Q$, a bipartite matching argument for $T$, since $T$'s entries are free parameters).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.357, Proposition 12.6.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.357, Proposition 12.6

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_IsNonsingularSub

namespace DiscreteConvex.MixedMatrices

/-- Proposition 12.6 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.357). A square mixed
matrix `A = Q + T` is nonsingular if and only if there exist `I ⊆ R` and `J ⊆ C` such that both
`Q[I,J]` and `T[R\I,C\J]` are nonsingular. -/
theorem mixed_matrix_nonsingular_iff {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T)
    (hsq : Fintype.card R = Fintype.card C) :
    IsNonsingularSub A (Finset.univ : Finset R) (Finset.univ : Finset C) ↔
      ∃ I : Finset R, ∃ J : Finset C, IsNonsingularSub Q I J ∧ IsNonsingularSub T Iᶜ Jᶜ := by sorry

end DiscreteConvex.MixedMatrices
