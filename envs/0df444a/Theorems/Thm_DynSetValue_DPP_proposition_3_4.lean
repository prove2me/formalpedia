-- Prove2me | Theorems.Thm_DynSetValue_DPP_proposition_3_4
-- name    : DynSetValue.DPP.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:21.116274+00:00
-- url     : https://prove2.me/theorems/5078b1af-0f0b-4289-994c-03c6252a6704
-- title:
--   Proposition 3.4 — boundedness, openness and compactness of set values
-- statement:
--   Under Assumption 3.1, for each history $(t,\omega)$ and positive $\varepsilon$, the relaxed set $\mathbb V_\varepsilon(t,\omega)$ is bounded and open. If $0<\varepsilon'<\varepsilon$, its closure lies in $\mathbb V_\varepsilon(t,\omega)$. The limiting set $\mathbb V(t,\omega)$ is compact, and it is nonempty if an $\varepsilon$-equilibrium exists for every positive $\varepsilon$.
--
--   $$
--   \overline{\mathbb V_{\varepsilon'}(t,\omega)}\subseteq
--   \mathbb V_\varepsilon(t,\omega),\qquad
--   \mathbb V(t,\omega)\text{ is compact}.
--   $$
--
--   This supplies the topological properties used when testing membership in the random continuation set.
-- source:
--   Feinstein, Rudloff, Zhang, Dynamic set values for nonzero sum games with multiple equilibriums, arXiv:2002.00449v2, p. 23, Proposition 3.4(i)–(iii)

import Mathlib
import Definitions.Def_DynSetValue_DPP_SetValue

open MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace DynSetValue.DPP

/-- Proposition 3.4, p. 23, including all three parts. -/
theorem proposition_3_4 {T : ℝ} (hT : 0 < T) {d N : ℕ}
    (G : Game T hT d N) (P0 : Measure (Ω T d))
    (hP0 : IsWiener hT P0) (h31 : Assumption31 G P0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω : Ω T d,
      (∀ ε : ℝ, 0 < ε →
        Bornology.IsBounded (Vε hT G P0 t ω ε) ∧
        IsOpen (Vε hT G P0 t ω ε)) ∧
      (∀ ε' ε : ℝ, 0 < ε' → ε' < ε →
        closure (Vε hT G P0 t ω ε') ⊆ Vε hT G P0 t ω ε) ∧
      IsCompact (V hT G P0 t ω) ∧
      ((∀ ε : ℝ, 0 < ε →
        ∃ α : Profile hT G, NEε hT G P0 t ω ε α) →
        (V hT G P0 t ω).Nonempty) := by sorry

end DynSetValue.DPP
