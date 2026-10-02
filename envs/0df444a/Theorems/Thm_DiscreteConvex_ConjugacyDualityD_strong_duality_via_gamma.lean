-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_strong_duality_via_gamma
-- name    : DiscreteConvex.ConjugacyDualityD.strong_duality_via_gamma
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:09:17.901212+00:00
-- url     : https://prove2.me/theorems/6274cb4a-556e-4e51-a8a5-9ca2a181040a
-- title:
--   Theorem 8.65 -- strong_duality_via_gamma
-- statement:
--   **Theorem 8.65** (p.242). For a feasible M-convex program with $B$ bounded: the primal optimal value equals $\gamma_r(0)$, which equals its own concave biconjugate at $0$, which equals the dual optimal value $\sup_y g_r(y)$; and the primal optimal solution set $\operatorname{opt}(P)$ equals the subdifferential of $-\gamma_r$ at $0$, which is nonempty.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.242, Theorem 8.65.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.242, Theorem 8.65

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConcaveConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SubDifferentialZEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRSmall
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GammaR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_OptP

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.65 (p.242). For a feasible M-convex program with `B` bounded, the primal optimal
value equals `γr(0)` and its concave biconjugate, matching the dual optimal value, with the
primal optimal set characterized by the subdifferential of `-γr` at `0`.  Murota, *Discrete Convex Analysis*, SIAM 2003, §8.4 works throughout with
integer-valued `c` and `r` (`c, r : Zⱽ → Z ∪ {+∞}`, pp. 235, 238); with real values the dual,
whose vectors are integral, loses strong duality (take `B = {0}`, `r` the indicator of
`{u₁ + u₂ = 0}` and `c` with slopes `-0.5` and `-0.3` along that line: no integer `y` has
`y₁ - y₂ ∈ [0.3, 0.5]`, so `φr••(0) = -∞ ≠ φr(0) = 0`).-/
theorem strong_duality_via_gamma (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r)
    (hB : ExchangeAxiomB B) (hBbdd : B.Finite) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r)
    (hr0 : r (fun _ => (0 : ℤ)) = 0) (hfeas : ∃ x ∈ B, c x ≠ ⊤) :
    PhiR c r B (fun _ => 0) = GammaR c r B (fun _ => 0) ∧
    GammaR c r B (fun _ => 0) = ConcaveConjE (ConcaveConjE (GammaR c r B)) (fun _ => 0) ∧
    ConcaveConjE (ConcaveConjE (GammaR c r B)) (fun _ => 0) =
      sSup {t : EReal | ∃ y, t = GRSmall c r B y} ∧
    OptP c B (PhiR c r B (fun _ => 0)) =
      SubDifferentialZEReal (fun x => -GammaR c r B x) (fun _ => 0) ∧
    (SubDifferentialZEReal (fun x => -GammaR c r B x) (fun _ => 0)).Nonempty := by sorry

end DiscreteConvex.ConjugacyDualityD
