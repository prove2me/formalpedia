-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialC_theorem_2_16_conjugacy_general_quadratic
-- name    : DiscreteConvex.CombinatorialC.theorem_2_16_conjugacy_general_quadratic
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:44:47.864009+00:00
-- url     : https://prove2.me/theorems/ac772b6c-4600-4615-a730-86926b03d6b5
-- title:
--   Theorem 2.16 -- conjugacy for general (possibly infinite) quadratic forms
-- statement:
--   Suppose $g$, $f$ (restricted quadratic forms, possibly $+\infty$) are conjugate. Then $g$ has translation submodularity iff $f$ has the M-natural exchange property.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.73, Theorem 2.16.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.73, Theorem 2.16

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_GenQF
import Definitions.Def_DiscreteConvex_CombinatorialC_ConjugateWT
import Definitions.Def_DiscreteConvex_CombinatorialC_ToEReal2
import Definitions.Def_DiscreteConvex_CombinatorialC_KerMat
import Definitions.Def_DiscreteConvex_CombinatorialC_OrthComp
import Definitions.Def_DiscreteConvex_CombinatorialC_TranslationSubmodularWT
import Definitions.Def_DiscreteConvex_CombinatorialC_MNatExchangeWT

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.73, Theorem 2.16, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Theorem 2.16.** Suppose that `g : Rⁿ → R ∪ {+∞}` in (2.24) and `f : Rⁿ → R ∪ {+∞}` in
(2.25) are conjugate to each other. Then `g` satisfies translation submodularity (SBF♮[R]) if
and only if `f` has exchange property (M♮-EXC[R]). -/
theorem theorem_2_16_conjugacy_general_quadratic {V : Type*} [Fintype V] [DecidableEq V]
    (L M : Matrix V V ℝ) (K Hs : Set (V → ℝ)) (hLsymm : L.IsSymm) (hMsymm : M.IsSymm)
    (hLpsd : L.PosSemidef) (hMpsd : M.PosSemidef)
    (hK : K = OrthComp (Hs ∩ KerMat M)) (hH : Hs = OrthComp (K ∩ KerMat L))
    (hconj : (∀ p : V → ℝ, ConjugateWT (GenQF M Hs) p = ToEReal2 (GenQF L K p)) ∧
      (∀ x : V → ℝ, ConjugateWT (GenQF L K) x = ToEReal2 (GenQF M Hs x))) :
    TranslationSubmodularWT (GenQF L K) ↔ MNatExchangeWT (GenQF M Hs) := by sorry

end DiscreteConvex.CombinatorialC
