-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_lagrangian_tilde_recovers_original
-- name    : DiscreteConvex.ConjugacyDualityD.lagrangian_tilde_recovers_original
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:12:19.759327+00:00
-- url     : https://prove2.me/theorems/6ba07fc3-4d3e-407c-8c66-5784239e9c01
-- title:
--   Proposition 8.62 -- lagrangian_tilde_recovers_original
-- statement:
--   **Proposition 8.62** (p.241). When $B$ is bounded (hence finite), the dual-of-dual reconstruction recovers the original data exactly: $\tilde K_r(x,y)=K_r(x,y)$ for all $x,y$, and $\tilde f(x) = F_r(x,0)$ for all $x$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Proposition 8.62.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Proposition 8.62

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_Fr
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KTildeR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_FTildeR

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.62 (p.241). When `B` is bounded, the dual-of-dual reconstruction recovers the
original Lagrangian and primal objective exactly.  Murota, *Discrete Convex Analysis*, SIAM 2003, §8.4 works throughout with
integer-valued `c` and `r` (`c, r : Zⱽ → Z ∪ {+∞}`, pp. 235, 238); with real values the dual,
whose vectors are integral, loses strong duality (take `B = {0}`, `r` the indicator of
`{u₁ + u₂ = 0}` and `c` with slopes `-0.5` and `-0.3` along that line: no integer `y` has
`y₁ - y₂ ∈ [0.3, 0.5]`, so `φr••(0) = -∞ ≠ φr(0) = 0`).-/
theorem lagrangian_tilde_recovers_original (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r)
    (hB : ExchangeAxiomB B) (hBbdd : B.Finite) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r)
    (hr0 : r (fun _ => (0 : ℤ)) = 0) :
    (∀ x y, KTildeR c r B x y = KR c r B x y) ∧
    (∀ x, FTildeR c r B x = ToEReal (Fr c r B x (fun _ => 0))) := by sorry

end DiscreteConvex.ConjugacyDualityD
