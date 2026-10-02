-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_supermodular_pair_conjugate_submodular
-- name    : DiscreteConvex.ConjugacyDualityB.supermodular_pair_conjugate_submodular
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:34:14.808381+00:00
-- url     : https://prove2.me/theorems/148e491f-ae3a-4a92-9d97-765da5311bc8
-- title:
--   Proposition 8.2 -- supermodular_pair_conjugate_submodular
-- statement:
--   **Proposition 8.2** (p.207). For a supermodular function $f$ in two variables, the Legendre-Fenchel transform $f^\bullet$ is submodular.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.207, Proposition 8.2.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.207, Proposition 8.2

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateRW
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SupermodularPair

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.2 (p.207). For a supermodular function `f` in two variables, `f•` is
submodular. -/
theorem supermodular_pair_conjugate_submodular (f : (Fin 2 → ℝ) → WithTop ℝ)
    (hf : SupermodularPair f) :
    ∀ p q : Fin 2 → ℝ, ConvexConjugateRW f p + ConvexConjugateRW f q ≥
      ConvexConjugateRW f (p ⊔ q) + ConvexConjugateRW f (p ⊓ q) := by sorry

end DiscreteConvex.ConjugacyDualityB
