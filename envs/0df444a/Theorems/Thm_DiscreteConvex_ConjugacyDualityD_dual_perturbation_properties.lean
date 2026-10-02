-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_dual_perturbation_properties
-- name    : DiscreteConvex.ConjugacyDualityD.dual_perturbation_properties
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:04:09.371373+00:00
-- url     : https://prove2.me/theorems/d7f66bf7-9105-4b04-a04f-181497eeb23b
-- title:
--   Proposition 8.63 -- dual_perturbation_properties
-- statement:
--   **Proposition 8.63** (p.241). Properties of the dual perturbation $G_r$ (for $B$ bounded, $c,r$ M-convex): (1) $G_r(y,0)=g_r(y)$; (2) for fixed $y$, $G_r(y,\cdot)$ is the negation of an L2-convex function (or identically $+\infty$); (3) for fixed $v$, $G_r(\cdot,v)$ is the negation of an L2-convex function, or identically $\pm\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Proposition 8.63.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Proposition 8.63

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsNegOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRSmall
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRBig

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.63 (p.241). Properties of the dual perturbation `Gr`.  Murota, *Discrete Convex Analysis*, SIAM 2003, §8.4 works throughout with
integer-valued `c` and `r` (`c, r : Zⱽ → Z ∪ {+∞}`, pp. 235, 238); with real values the dual,
whose vectors are integral, loses strong duality (take `B = {0}`, `r` the indicator of
`{u₁ + u₂ = 0}` and `c` with slopes `-0.5` and `-0.3` along that line: no integer `y` has
`y₁ - y₂ ∈ [0.3, 0.5]`, so `φr••(0) = -∞ ≠ φr(0) = 0`).-/
theorem dual_perturbation_properties (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r)
    (hB : ExchangeAxiomB B) (hBbdd : B.Finite) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r)
    (hr0 : r (fun _ => (0 : ℤ)) = 0) :
    (∀ y, GRBig c r B y (fun _ => 0) = GRSmall c r B y) ∧
    (∀ y, IsNegOf L2Convex (fun v => GRBig c r B y v) ∨ ∀ v, GRBig c r B y v = ⊤) ∧
    (∀ v, IsNegOf L2Convex (fun y => GRBig c r B y v) ∨ (∀ y, GRBig c r B y v = ⊥) ∨
      (∀ y, GRBig c r B y v = ⊤)) := by sorry

end DiscreteConvex.ConjugacyDualityD
