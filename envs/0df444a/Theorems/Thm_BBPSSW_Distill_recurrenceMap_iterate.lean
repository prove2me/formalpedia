-- Prove2me | Theorems.Thm_BBPSSW_Distill_recurrenceMap_iterate
-- name    : BBPSSW.Distill.recurrenceMap_iterate
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:15.647555+00:00
-- url     : https://prove2.me/theorems/ab02a2bf-ac0f-4330-b975-1ab78228bcde
-- title:
--   The recurrence map is continuous, raises $F$ on $(1/2,1)$, and its iterates tend to $1$
-- statement:
--   Let $F'$ be the recurrence map of Eq. (7). Then
--
--   1. $F'$ is continuous;
--   2. $F<F'(F)$ for every $\tfrac12<F<1$;
--   3. for every $\tfrac12<F_0\le1$, the iterates $F'^{\,k}(F_0)\to1$ as $k\to\infty$.
--
--   Hence iterating the recurrence step distills Werner states of arbitrarily high purity $F_{\text{out}}<1$ from any input purity $F_{\text{in}}>\tfrac12$.
--
--   Differences from the source:
--   - generalization: iteration can distill Werner states of arbitrarily high purity Fout < 1 from any Fin > 1/2 → the iterates converge to 1 for every 1/2 < F₀ ≤ 1, and F′ is continuous on all of ℝ; reason: convergence to 1 implies every Fout < 1 is exceeded; continuity on ℝ implies continuity on (1/2, 1)
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 3, unnumbered ("Because F′(F) is continuous and exceeds F over the entire range 1/2 < F < 1 …")

import Mathlib
import Definitions.Def_BBPSSW_Distill_recurrenceMap

open Filter Topology

namespace BBPSSW.Distill

/-- **The recurrence map is continuous, raises F, and its iterates tend to 1.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 3 (unnumbered): "Because F′(F) is continuous and exceeds F over the entire range
1/2 < F < 1, iteration of the above protocol can distill Werner states of arbitrarily high
purity Fout < 1 from a supply of input mixed states M of any purity Fin > 1/2."

With `F′ = recurrenceMap` (Eq. (7)):
1. `F′` is continuous;
2. `F < F′(F)` for every `1/2 < F < 1`;
3. for every `1/2 < F₀ ≤ 1`, the iterates `F′^[k](F₀)` tend to `1` as `k → ∞`.

**Formalization Note.** Clause 3 is the mathematical content of "can distill Werner states of
arbitrarily high purity Fout < 1"; convergence to 1 implies that every `Fout < 1` is exceeded
(a generalization). Clause 1 holds on all of ℝ, since the denominator of Eq. (7) never
vanishes. -/
theorem recurrenceMap_iterate :
    Continuous recurrenceMap ∧
      (∀ F : ℝ, 1 / 2 < F → F < 1 → F < recurrenceMap F) ∧
      ∀ F₀ : ℝ, 1 / 2 < F₀ → F₀ ≤ 1 →
        Tendsto (fun k : ℕ => recurrenceMap^[k] F₀) atTop (𝓝 1) := by sorry

end BBPSSW.Distill
