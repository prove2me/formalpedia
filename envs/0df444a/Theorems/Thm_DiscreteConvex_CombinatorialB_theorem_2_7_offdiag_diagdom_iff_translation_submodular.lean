-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialB_theorem_2_7_offdiag_diagdom_iff_translation_submodular
-- name    : DiscreteConvex.CombinatorialB.theorem_2_7_offdiag_diagdom_iff_translation_submodular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:32:52.641329+00:00
-- url     : https://prove2.me/theorems/b81719d8-e63a-4556-ae99-0257598537c2
-- title:
--   Theorem 2.7 -- off-diagonal nonpositivity + diagonal dominance iff translation submodularity
-- statement:
--   For a symmetric matrix $L$: off-diagonal nonpositivity (2.9) together with diagonal dominance (2.10) holds if and only if $g(p)=\tfrac12p^\top Lp$ has translation submodularity (SBF-natural[R]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.65-66, Theorem 2.7.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.65-66, Theorem 2.7

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_OffDiagNonpos
import Definitions.Def_DiscreteConvex_CombinatorialB_DiagDominance
import Definitions.Def_DiscreteConvex_CombinatorialB_QF
import Definitions.Def_DiscreteConvex_CombinatorialB_TranslationSubmodular

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, pp.65-66, Theorem 2.7, in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Theorem 2.7.** For a symmetric matrix `L`, off-diagonal nonpositivity (2.9) together with
diagonal dominance (2.10) is equivalent to translation submodularity (SBF-natural[R]) of
`g(p) = (1/2)p⊤Lp`. -/
theorem theorem_2_7_offdiag_diagdom_iff_translation_submodular {V : Type*} [Fintype V]
    [DecidableEq V] (L : Matrix V V ℝ) (hsymm : L.IsSymm) :
    (OffDiagNonpos L ∧ DiagDominance L) ↔ TranslationSubmodular (QF L) := by sorry

end DiscreteConvex.CombinatorialB
