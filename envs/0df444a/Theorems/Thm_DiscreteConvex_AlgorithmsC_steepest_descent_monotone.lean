-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsC_steepest_descent_monotone
-- name    : DiscreteConvex.AlgorithmsC.steepest_descent_monotone
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T04:35:59.50382+00:00
-- url     : https://prove2.me/theorems/a05a6bd3-98cc-4147-82ec-316520a32486
-- title:
--   Proposition 10.30 -- steepest_descent_monotone
-- statement:
--   **Proposition 10.30** (p.306). In the steepest descent algorithm with the minimal-minimizer tie-breaking rule (10.33), $p\le p^*$ implies $p+\chi_X\le p^*$ for the minimal minimizer $X$ of $\rho_p$, where $p^*$ is any minimizer of $g$.
--
--   **Scope note.** The book's own trailing corollary ("hence the number of iterations is bounded by $\|p^\circ-p^*\|_1$") is an iteration-count bound and is omitted; see `HARD.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.306, Proposition 10.30.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.306, Proposition 10.30

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_ArgMin
import Definitions.Def_DiscreteConvex_AlgorithmsC_SBF
import Definitions.Def_DiscreteConvex_AlgorithmsC_IsMinimalMinimizerWT
import Definitions.Def_DiscreteConvex_AlgorithmsC_RhoP

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.30 (p.306). In the steepest descent algorithm with the minimal-minimizer
tie-breaking rule (10.33), `p ≤ p*` implies `p+χ_X ≤ p*` for the minimal minimizer `X` of `ρ_p`,
where `p*` is any minimizer of `g`. -/
theorem steepest_descent_monotone (g : (V → ℤ) → WithTop ℝ) (hg : SBF g) (p pstar : V → ℤ)
    (hpstar : pstar ∈ ArgMin g) (hple : ∀ v, p v ≤ pstar v) (X : Finset V)
    (hX : IsMinimalMinimizerWT (RhoP g p) X) :
    ∀ v, p v + (if v ∈ X then (1:ℤ) else 0) ≤ pstar v := by sorry

end DiscreteConvex.AlgorithmsC
