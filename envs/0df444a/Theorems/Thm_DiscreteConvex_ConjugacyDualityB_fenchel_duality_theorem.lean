-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_fenchel_duality_theorem
-- name    : DiscreteConvex.ConjugacyDualityB.fenchel_duality_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:35:15.725867+00:00
-- url     : https://prove2.me/theorems/c9c7af9d-048b-49f3-967f-65d91e7863e3
-- title:
--   Theorem 8.21 -- fenchel_duality_theorem
-- statement:
--   **Theorem 8.21** (Fenchel-type duality theorem; p.222), parts (1)-(2). For an M$^\natural$-convex/concave (resp. L$^\natural$-convex/concave) pair with the separation-theorem domain hypothesis, $\inf\{f-h\}=\sup\{h^\circ-f^\bullet\}$, and if finite the supremum is attained.
--
--   **Formalization Note.** Parts (3)-(4), the integer-valued refinement requiring both the infimum and the supremum to be attained by integer points, are not restated here: they need a genuinely separate integer-attainment argument beyond the real-attainment claim of parts (1)-(2), and no other result in this chunk needs it. See `HARD.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.222, Theorem 8.21.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.222, Theorem 8.21

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateZR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConcaveConjugateZR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomERealConcave
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_InfDiff
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SupDualGap

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.21 (Fenchel-type duality theorem; p.222), parts (1)-(2). Strong duality between an
M♮-(resp. L♮-)convex/concave pair and their conjugates, with the supremum attained. -/
theorem fenchel_duality_theorem :
    (∀ f h2 : (V → ℤ) → WithTop ℝ, MNaturalConvex f → MNaturalConvex h2 →
      ((DomZ f ∩ DomZ h2).Nonempty ∨
        (DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h2)).Nonempty) →
      InfDiff f h2 = SupDualGap f h2 ∧
      (InfDiff f h2 ≠ ⊤ → InfDiff f h2 ≠ ⊥ →
        ∃ p : V → ℝ, p ∈ DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h2) ∧
          ConcaveConjugateZR h2 p - ConvexConjugateZR f p = SupDualGap f h2)) ∧
    (∀ g k2 : (V → ℤ) → WithTop ℝ, LNaturalConvex g → LNaturalConvex k2 →
      ((DomZ g ∩ DomZ k2).Nonempty ∨
        (DomEReal (ConvexConjugateZR g) ∩ DomERealConcave (ConcaveConjugateZR k2)).Nonempty) →
      InfDiff g k2 = SupDualGap g k2 ∧
      (InfDiff g k2 ≠ ⊤ → InfDiff g k2 ≠ ⊥ →
        ∃ x : V → ℝ, x ∈ DomEReal (ConvexConjugateZR g) ∩ DomERealConcave (ConcaveConjugateZR k2) ∧
          ConcaveConjugateZR k2 x - ConvexConjugateZR g x = SupDualGap g k2)) := by sorry

end DiscreteConvex.ConjugacyDualityB
