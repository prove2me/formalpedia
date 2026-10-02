-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_m_convex_perturbation_properties
-- name    : DiscreteConvex.ConjugacyDualityD.m_convex_perturbation_properties
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:02:35.223139+00:00
-- url     : https://prove2.me/theorems/c0d46a13-2382-4230-bbf8-1df37ba98f13
-- title:
--   Proposition 8.55 -- m_convex_perturbation_properties
-- statement:
--   **Proposition 8.55** (p.239). The perturbation $F_r(x,u)=c(x)+\delta_B(x+u)+r(u)$ legitimately embeds an M-convex program: (i) $F_r(x,0)=c(x)$; (ii) $F_0(x,\cdot)$ is M-convex in $u$ (or identically $+\infty$); (iii) $F_r(x,\cdot)$ is M2-convex in $u$ (or identically $+\infty$); (iv) $F_r(x,\cdot)$ is self-biconjugate; (v) $F_r(x,u)$ equals the displayed sup-representation via $K_r$; (vi) if $c$ is M-convex, $F_r(\cdot,u)$ is M2-convex in $x$ (or identically $+\infty$) for every $u$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.239, Proposition 8.55.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.239, Proposition 8.55

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_F0
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_Fr
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConvexConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KR

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.55 (p.239). The perturbation `Fr` legitimately embeds the M-convex program:
it recovers `c` at `u=0`, is M-(resp. M2-)convex in `u`, is self-biconjugate in `u`, satisfies
the displayed sup-representation, and is M2-convex in `x` when `c` is M-convex.  Murota, *Discrete Convex Analysis*, SIAM 2003, §8.4 works throughout with
integer-valued `c` and `r` (`c, r : Zⱽ → Z ∪ {+∞}`, pp. 235, 238); with real values the dual,
whose vectors are integral, loses strong duality (take `B = {0}`, `r` the indicator of
`{u₁ + u₂ = 0}` and `c` with slopes `-0.5` and `-0.3` along that line: no integer `y` has
`y₁ - y₂ ∈ [0.3, 0.5]`, so `φr••(0) = -∞ ≠ φr(0) = 0`).-/
theorem m_convex_perturbation_properties (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r)
    (hB : ExchangeAxiomB B) (hr : MExchangeAxiom r) (hr0 : r (fun _ => (0 : ℤ)) = 0) :
    (∀ x, Fr c r B x (fun _ => 0) = c x) ∧
    (∀ x, MExchangeAxiom (F0 c B x) ∨ ∀ u, F0 c B x u = ⊤) ∧
    (∀ x, M2Convex (Fr c r B x) ∨ ∀ u, Fr c r B x u = ⊤) ∧
    (∀ x, ConvexConjE (ConvexConjE (fun u => ToEReal (Fr c r B x u))) =
      fun u => ToEReal (Fr c r B x u)) ∧
    (∀ x u, ToEReal (Fr c r B x u) =
      sSup {t : EReal | ∃ y, t = KR c r B x y - ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)}) ∧
    (MExchangeAxiom c →
      ∀ u, M2Convex (fun x => Fr c r B x u) ∨ ∀ x, Fr c r B x u = ⊤) := by sorry

end DiscreteConvex.ConjugacyDualityD
