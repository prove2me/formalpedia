-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsB_eta_nonpos_gives_maximal_minimizer
-- name    : DiscreteConvex.AlgorithmsB.eta_nonpos_gives_maximal_minimizer
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T04:11:46.921265+00:00
-- url     : https://prove2.me/theorems/8f39e2de-7e51-4c3f-94ab-cd66d4025d3c
-- title:
--   Proposition 10.24 -- eta_nonpos_gives_maximal_minimizer
-- statement:
--   **Proposition 10.24** (p.301). In the IFF fixing algorithm's terminal state, $\eta\le0$ implies $V\setminus H$ is the maximal minimizer of $\rho$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, Proposition 10.24.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, Proposition 10.24

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsMaximalMinimizer
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsMinimizerOf
import Definitions.Def_DiscreteConvex_AlgorithmsB_Eta

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.24 (p.301). In the IFF fixing algorithm's terminal state, `η ≤ 0` implies
`V∖H` is the maximal minimizer of `ρ`. The statement is about that terminal state, so it carries
the algorithm's invariants: no element of `H` lies in any minimizer, every element of `Z` lies in
every minimizer, and a minimizer containing `Γ(u)` contains `Γ(w)` for every arc `(u,w)` of `F`.
Without them `V = {a,b}`, `U = {u}`, `Γ(u) = {a}`, `Z = ∅`, `H = {b}`, `F = ∅` and
`ρ(X) = -1` iff `b ∈ X` give `η = 0` while the maximal minimizer is `{a,b}`, not `V ∖ H = {a}`. -/
theorem eta_nonpos_gives_maximal_minimizer {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (rho : Finset V → ℤ) (hrho : Submodular rho) (Gamma : U → Finset V) (Z H : Finset V)
    (hpart1 : ∀ u, Gamma u ⊆ Finset.univ \ (Z ∪ H)) (hpart2 : ∀ u, (Gamma u).Nonempty)
    (hpart3 : ∀ u v, u ≠ v → Disjoint (Gamma u) (Gamma v))
    (hpart4 : Finset.univ = (Finset.univ.biUnion Gamma) ∪ Z ∪ H) (F : U → U → Prop)
    (hinvH : ∀ W, IsMinimizerOf rho W → Disjoint H W)
    (hinvZ : ∀ W, IsMinimizerOf rho W → Z ⊆ W)
    (hinvF : ∀ u w, F u w → ∀ W, IsMinimizerOf rho W → Gamma u ⊆ W → Gamma w ⊆ W)
    (heta : Eta rho Gamma Z F ≤ 0) :
    IsMaximalMinimizer rho (Finset.univ \ H) := by sorry

end DiscreteConvex.AlgorithmsB
