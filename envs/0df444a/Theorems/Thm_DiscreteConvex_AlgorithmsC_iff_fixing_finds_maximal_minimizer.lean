-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsC_iff_fixing_finds_maximal_minimizer
-- name    : DiscreteConvex.AlgorithmsC.iff_fixing_finds_maximal_minimizer
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T04:42:26.458264+00:00
-- url     : https://prove2.me/theorems/0d776e3a-bf39-41be-9268-69e6c8624aee
-- title:
--   Proposition 10.28 -- iff_fixing_finds_maximal_minimizer
-- statement:
--   **Proposition 10.28** (p.304). The IFF fixing algorithm finds the maximal minimizer of $\rho$ — i.e. it terminates in the state Proposition 10.24 (mission `34-ch10b-algorithms`) characterizes, restated here with freshly redeclared apparatus since this draft cannot import that sibling.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.304, Proposition 10.28.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.304, Proposition 10.28

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsC_IsMaximalMinimizer
import Definitions.Def_DiscreteConvex_AlgorithmsC_IsMinimizerOf
import Definitions.Def_DiscreteConvex_AlgorithmsC_Eta

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.28 (p.304). The IFF fixing algorithm finds the maximal minimizer of `ρ`
(i.e. it terminates in the state Proposition 10.24 characterizes). The statement is about that
terminal state, so, as in Proposition 10.24, it carries the algorithm's invariants: no element of
`H` lies in any minimizer, every element of `Z` lies in every minimizer, and a minimizer
containing `Γ(u)` contains `Γ(w)` for every arc `(u,w)` of `F`. Without them `V = {a,b}`,
`U = {u}`, `Γ(u) = {a}`, `Z = ∅`, `H = {b}`, `F = ∅` and `ρ(X) = -1` iff `b ∈ X` give `η = 0` while
the maximal minimizer is `{a,b}`, not `V ∖ H = {a}`. -/
theorem iff_fixing_finds_maximal_minimizer {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (rho : Finset V → ℤ) (hrho : Submodular rho) (Gamma : U → Finset V) (Z H : Finset V)
    (hpart1 : ∀ u, Gamma u ⊆ Finset.univ \ (Z ∪ H)) (hpart2 : ∀ u, (Gamma u).Nonempty)
    (hpart3 : ∀ u v, u ≠ v → Disjoint (Gamma u) (Gamma v))
    (hpart4 : Finset.univ = (Finset.univ.biUnion Gamma) ∪ Z ∪ H) (F : U → U → Prop)
    (hinvH : ∀ W, IsMinimizerOf rho W → Disjoint H W)
    (hinvZ : ∀ W, IsMinimizerOf rho W → Z ⊆ W)
    (hinvF : ∀ u w, F u w → ∀ W, IsMinimizerOf rho W → Gamma u ⊆ W → Gamma w ⊆ W)
    (heta : Eta rho Gamma Z F ≤ 0) :
    IsMaximalMinimizer rho (Finset.univ \ H) := by sorry

end DiscreteConvex.AlgorithmsC
