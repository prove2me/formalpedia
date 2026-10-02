-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialB_theorem_2_11_conjugacy_sbf_mexch
-- name    : DiscreteConvex.CombinatorialB.theorem_2_11_conjugacy_sbf_mexch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:34:42.103984+00:00
-- url     : https://prove2.me/theorems/c841bd14-7ae3-49fb-8b23-fa2da3023f18
-- title:
--   Theorem 2.11 -- conjugacy between translation submodularity and the M-natural exchange property (GOAL)
-- statement:
--   Suppose strictly convex quadratic forms $g(p)=\tfrac12p^\top Lp$ and $f(x)=\tfrac12x^\top Mx$ are conjugate to each other. Then $g$ has translation submodularity (SBF-natural[R]) if and only if $f$ has the exchange property (M-natural-EXC[R]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, Theorem 2.11, the main theorem of section 2.1.3.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, Theorem 2.11

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_QF
import Definitions.Def_DiscreteConvex_CombinatorialB_Conjugate
import Definitions.Def_DiscreteConvex_CombinatorialB_TranslationSubmodular
import Definitions.Def_DiscreteConvex_CombinatorialB_MNatExchangeR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.69, Theorem 2.11 — the main theorem of
section 2.1.3 — in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Theorem 2.11** (goal). Suppose that strictly convex quadratic forms `g(p) = (1/2)p⊤Lp`
and `f(x) = (1/2)x⊤Mx` are conjugate to each other (with respect to the Legendre-Fenchel
transformation (1.6)). Then `g` satisfies translation submodularity (SBF-natural[R]) if and
only if `f` has the exchange property (M-natural-EXC[R]). -/
theorem theorem_2_11_conjugacy_sbf_mexch {V : Type*} [Fintype V] [DecidableEq V]
    (M L : Matrix V V ℝ) (hMsymm : M.IsSymm) (hLsymm : L.IsSymm) (hMpd : M.PosDef)
    (hLpd : L.PosDef)
    (hconj : (∀ p : V → ℝ, Conjugate (QF M) p = ((QF L p : ℝ) : EReal)) ∧
      (∀ x : V → ℝ, Conjugate (QF L) x = ((QF M x : ℝ) : EReal))) :
    TranslationSubmodular (QF L) ↔ MNatExchangeR (QF M) := by sorry

end DiscreteConvex.CombinatorialB
