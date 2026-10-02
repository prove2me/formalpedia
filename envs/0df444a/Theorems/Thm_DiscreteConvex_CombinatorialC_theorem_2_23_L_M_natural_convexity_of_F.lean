-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialC_theorem_2_23_L_M_natural_convexity_of_F
-- name    : DiscreteConvex.CombinatorialC.theorem_2_23_L_M_natural_convexity_of_F
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:46:44.579928+00:00
-- url     : https://prove2.me/theorems/d1d71442-4089-4392-9732-0e1ddd45ca43
-- title:
--   Theorem 2.23 -- L-natural/M-natural convexity of F in parallel/series arc data (GOAL)
-- statement:
--   For $P$ parallel and $S$ series arc sets: $F$ is L-natural-convex in $w_P$, M-natural-concave in $c_P$, M-natural-convex in $w_S$, L-natural-concave in $c_S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84, Theorem 2.23.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84, Theorem 2.23

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_FVal
import Definitions.Def_DiscreteConvex_CombinatorialC_NonnegOrthant
import Definitions.Def_DiscreteConvex_CombinatorialC_TranslationSubmodularOn
import Definitions.Def_DiscreteConvex_CombinatorialC_MNatExchangeROn
import Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_ExtendOn
import Definitions.Def_DiscreteConvex_CombinatorialC_TranslationSubmodular
import Definitions.Def_DiscreteConvex_CombinatorialC_MNatExchangeR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.84, Theorem 2.23 — the goal of this mission —
in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Theorem 2.23** (goal). Let `P` be a parallel arc set and `S` a series arc set. (1) `F` is
L-natural-convex in `w_P` and M-natural-concave in `c_P`. (2) `F` is M-natural-convex in `w_S`
and L-natural-concave in `c_S`. Concavity of `h` is recorded as the exchange/translation-
submodularity property of `-h` (the standard "concave iff negation convex" convention). -/
theorem theorem_2_23_L_M_natural_convexity_of_F {V A : Type*} [Fintype A] [Fintype V]
    [DecidableEq V] [DecidableEq A] (src dst : A → V) (P S : Finset A)
    (hP : IsParallelArcSet src dst P) (hS : IsSeriesArcSet src dst S) (w0 c0 : A → ℝ)
    (hc0 : 0 ≤ c0) :
    (TranslationSubmodular (fun wP : P → ℝ => FVal src dst (ExtendOn w0 P wP) c0) ∧
        MNatExchangeROn NonnegOrthant
          (fun cP : P → ℝ => -(FVal src dst w0 (ExtendOn c0 P cP)))) ∧
      (MNatExchangeR (fun wS : S → ℝ => FVal src dst (ExtendOn w0 S wS) c0) ∧
        TranslationSubmodularOn NonnegOrthant
          (fun cS : S → ℝ => -(FVal src dst w0 (ExtendOn c0 S cS)))) := by sorry

end DiscreteConvex.CombinatorialC
