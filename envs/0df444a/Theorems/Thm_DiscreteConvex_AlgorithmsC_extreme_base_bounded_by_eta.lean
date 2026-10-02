-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsC_extreme_base_bounded_by_eta
-- name    : DiscreteConvex.AlgorithmsC.extreme_base_bounded_by_eta
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T04:42:19.325957+00:00
-- url     : https://prove2.me/theorems/2438012f-a9ea-483c-9bf5-9f127aa3161a
-- title:
--   Proposition 10.26 -- extreme_base_bounded_by_eta
-- statement:
--   **Proposition 10.26** (p.303). The core inequality behind the legitimacy of the fixing procedures Fix$^\pm$: for a submodular $\tilde\rho$ derived via $\Gamma,Z$ and any $u$, an extreme-base coordinate $y(u)$ computed from a tight set $Y\supseteq R(u)$ is bounded by $\eta$.
--
--   **Formalization note.** This extracts the case-independent core fact the book's own proof establishes and reuses identically across Cases (i)-(iii) of Proposition 10.24 (already placed in mission `34-ch10b-algorithms`); the case-by-case verification against that proof's own internal objects (Case (i)/(ii)/(iii), conditions (10.27)-(10.29)) is not separately replicated. See `HARD.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.303, Proposition 10.26.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.303, Proposition 10.26

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsC_RhoTilde
import Definitions.Def_DiscreteConvex_AlgorithmsC_ReachSet
import Definitions.Def_DiscreteConvex_AlgorithmsC_Eta

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.26 (p.303). The core inequality behind the legitimacy of Fix±: for a
submodular `ρ̃` derived via `Γ,Z` and any `u`, an extreme-base coordinate `y(u)` computed from a
tight set `Y ⊇ R(u)` is bounded by `η`. This is the case-independent fact the book's own proof
establishes and reuses identically across Cases (i)-(iii) of Proposition 10.24; the case-by-case
verification against that proof's own internal objects is not separately replicated (see
`HARD.md`/`MODERATION_NOTES.md`). The inequality rests on submodularity of
`ρ̃(Y) = ρ(Γ(Y) ∪ Z) - ρ(Z)`, which needs the blocks `Γ(u)` pairwise disjoint as the algorithm
keeps them: with `U = {u,w}`, `V = {a}`, `Γ(u) = Γ(w) = {a}`, `Z = ∅`, `F = ∅`, `ρ(∅) = 0` and
`ρ({a}) = -1`, `η = -1` while `Y = {u,w}` gives `y(u) = 0`. -/
theorem extreme_base_bounded_by_eta {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (rho : Finset V → ℤ) (hrho : Submodular rho) (Gamma : U → Finset V) (Z : Finset V)
    (hGammaDisj : ∀ u v : U, u ≠ v → Disjoint (Gamma u) (Gamma v))
    (F : U → U → Prop) (u : U) (yu : ℤ) (Y : Finset U) (hY : ReachSet F u ⊆ Y)
    (hyu : yu = RhoTilde rho Gamma Z Y - RhoTilde rho Gamma Z (Y.erase u)) :
    (yu : ℝ) ≤ (Eta rho Gamma Z F : ℝ) := by sorry

end DiscreteConvex.AlgorithmsC
