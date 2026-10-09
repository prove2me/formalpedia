-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_m_convex_strong_duality
-- name    : DiscreteConvex.ConjugacyDualityD.m_convex_strong_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T02:04:10.652859+00:00
-- url     : https://prove2.me/theorems/0fc8b5cd-f633-4deb-b36a-886151303493
-- title:
--   Theorem 8.59 -- m_convex_strong_duality
-- statement:
--   **Theorem 8.59** (Strong duality; p.240-241). GOAL. For an M-convex program (feasible: $\exists x\in B$, $c(x)\ne+\infty$; bounded below: $\varphi_r(0)\ne-\infty$): the primal optimal value equals its convex biconjugate at $0$, which equals the dual optimal value $\sup_y g_r(y)$; the dual-optimal set equals the negated integer subdifferential of $\varphi_r$ at $0$; and that subdifferential is nonempty (so the dual optimum is attained).
--
--   This is the strong-duality theorem explicitly named by the book and explicitly deferred by mission `11-conjugacy-ii-lagrange`'s own `STATUS.md`, which noted it needs the specific M-convex perturbation $F_r$ (Eq. (8.61)) and Propositions 8.55-8.56/Theorems 8.57-8.58 as prerequisites — all now built in this chunk.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240-241, Theorem 8.59.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240-241, Theorem 8.59

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConvexConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SubDifferentialZEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRSmall

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.59 (Strong duality; p.240-241). GOAL. For a feasible, bounded-below M-convex
program, the primal optimal value equals the regularized dual optimal value, and the dual
optimal set is the (negated) integer subdifferential of `φr` at `0`.  Murota, *Discrete Convex Analysis*, SIAM 2003, §8.4 works throughout with
integer-valued `c` and `r` (`c, r : Zⱽ → Z ∪ {+∞}`, pp. 235, 238); with real values the dual,
whose vectors are integral, loses strong duality (take `B = {0}`, `r` the indicator of
`{u₁ + u₂ = 0}` and `c` with slopes `-0.5` and `-0.3` along that line: no integer `y` has
`y₁ - y₂ ∈ [0.3, 0.5]`, so `φr••(0) = -∞ ≠ φr(0) = 0`).-/
theorem m_convex_strong_duality (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r)
    (hB : ExchangeAxiomB B) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r)
    (hr0 : r (fun _ => (0 : ℤ)) = 0) (hfeas : ∃ x ∈ B, c x ≠ ⊤)
    (hbdd : PhiR c r B (fun _ => 0) ≠ ⊥) :
    PhiR c r B (fun _ => 0) = ConvexConjE (ConvexConjE (PhiR c r B)) (fun _ => 0) ∧
    ConvexConjE (ConvexConjE (PhiR c r B)) (fun _ => 0) =
      sSup {t : EReal | ∃ y, t = GRSmall c r B y} ∧
    {y | GRSmall c r B y = sSup {t : EReal | ∃ y', t = GRSmall c r B y'}} =
      (fun p => fun v => -p v) '' SubDifferentialZEReal (PhiR c r B) (fun _ => 0) ∧
    (SubDifferentialZEReal (PhiR c r B) (fun _ => 0)).Nonempty := by sorry

end DiscreteConvex.ConjugacyDualityD
