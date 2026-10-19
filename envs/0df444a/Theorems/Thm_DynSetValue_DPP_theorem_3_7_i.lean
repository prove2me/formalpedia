-- Prove2me | Theorems.Thm_DynSetValue_DPP_theorem_3_7_i
-- name    : DynSetValue.DPP.theorem_3_7_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:56.274979+00:00
-- url     : https://prove2.me/theorems/b097361c-e4c7-4498-8412-18010c527468
-- title:
--   Theorem 3.7(i) — stability of relaxed value sets
-- statement:
--   Under Assumptions 3.1 and 3.6(i), for any $0<\varepsilon_1<\varepsilon_2$ there exists $\delta>0$ such that, whenever two histories are within $\delta$ in the metric $\mathbf d$,
--
--   $$
--   \mathbb V_{\varepsilon_1}(\widetilde t,\widetilde\omega)
--   \subseteq\mathbb V_{\varepsilon_2}(t,\omega).
--   $$
--
--   The conclusion holds uniformly over all admissible controls and all histories in the horizon. It relates nearby equilibrium-value sets without selecting an equilibrium.
-- source:
--   Feinstein, Rudloff, Zhang, Dynamic set values for nonzero sum games with multiple equilibriums, arXiv:2002.00449v2, p. 24, Theorem 3.7(i), equation (3.3)

import Mathlib
import Definitions.Def_DynSetValue_DPP_SetValue

open MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace DynSetValue.DPP

/-- Theorem 3.7(i), equation (3.3), p. 24. -/
theorem theorem_3_7_i {T : ℝ} (hT : 0 < T) {d N : ℕ}
    (G : Game T hT d N) (P0 : Measure (Ω T d))
    (hP0 : IsWiener hT P0) (h31 : Assumption31 G P0)
    (h36i : Assumption36i G)
    (ε₁ ε₂ : ℝ) (hε₁ : 0 < ε₁) (hε : ε₁ < ε₂) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
        ∀ ω ω', distD hT t ω t' ω' ≤ δ →
          Vε hT G P0 t' ω' ε₁ ⊆ Vε hT G P0 t ω ε₂ := by sorry

end DynSetValue.DPP
