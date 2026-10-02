-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_dual_optimal_value_properties
-- name    : DiscreteConvex.ConjugacyDualityD.dual_optimal_value_properties
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:05:47.577678+00:00
-- url     : https://prove2.me/theorems/65976454-9b03-40cb-9dff-8e60e6c1efae
-- title:
--   Theorem 8.64 -- dual_optimal_value_properties
-- statement:
--   **Theorem 8.64** (p.241-242). The dual optimal-value function $\gamma_r$ recovers the primal perturbation via concave conjugacy: $F_r(x,0) = -\gamma_r^{\bullet}(-x)$ (concave Legendre-Fenchel transform); and $\gamma_r$ is itself the negation of an L2-convex function, or identically $+\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241-242, Theorem 8.64.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241-242, Theorem 8.64

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_Fr
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConcaveConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsNegOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GammaR

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.64 (p.241-242). The dual optimal-value function `γr` recovers the primal
perturbation via concave conjugacy, and is itself L2-concave.  Murota, *Discrete Convex Analysis*, SIAM 2003, §8.4 works throughout with
integer-valued `c` and `r` (`c, r : Zⱽ → Z ∪ {+∞}`, pp. 235, 238); with real values the dual,
whose vectors are integral, loses strong duality (take `B = {0}`, `r` the indicator of
`{u₁ + u₂ = 0}` and `c` with slopes `-0.5` and `-0.3` along that line: no integer `y` has
`y₁ - y₂ ∈ [0.3, 0.5]`, so `φr••(0) = -∞ ≠ φr(0) = 0`).-/
theorem dual_optimal_value_properties (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r)
    (hB : ExchangeAxiomB B) (hBbdd : B.Finite) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r)
    (hr0 : r (fun _ => (0 : ℤ)) = 0) :
    (∀ x, ToEReal (Fr c r B x (fun _ => 0)) = -(ConcaveConjE (GammaR c r B) (fun v => -x v))) ∧
    (IsNegOf L2Convex (GammaR c r B) ∨ ∀ v, GammaR c r B v = ⊤) := by sorry

end DiscreteConvex.ConjugacyDualityD
