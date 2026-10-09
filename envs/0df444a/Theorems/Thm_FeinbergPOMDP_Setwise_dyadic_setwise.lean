-- Prove2me | Theorems.Thm_FeinbergPOMDP_Setwise_dyadic_setwise
-- name    : FeinbergPOMDP.Setwise.dyadic_setwise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:38.843536+00:00
-- url     : https://prove2.me/theorems/ec6cf341-93a4-4649-bbdc-6a9faaa102f5
-- title:
--   Example 4.1 — dyadic observation laws converge setwise
-- statement:
--   Let $m$ be Lebesgue probability measure on $[0,1]$. For each positive integer $n$, let $m^{(n)}=f^{(n)}m$, where $f^{(n)}$ is the dyadic density in equation (4.1). For every Borel set $C\subseteq[0,1]$,
--
--   $$
--   m^{(n)}(C)\longrightarrow m(C)\qquad(n\to\infty).
--   $$
--
--   Thus the oscillating observation laws converge setwise even though their densities do not approach the constant density one in total variation. This is the measure convergence used to establish continuity of the observation kernel.
--
--   **Formalization Note** Lean's sequence index $k\ge0$ denotes the paper's $n=k+1$.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Example 4.1, pp. 13–14, unnumbered final sentence of the first part

import Mathlib
import Definitions.Def_FeinbergPOMDP_Setwise_Model

namespace FeinbergPOMDP.Setwise

open MeasureTheory Filter
open scoped Topology

/-- Feinberg–Kasyanov–Zgurovsky, arXiv:1401.2168v2, Example 4.1,
pp. 13–14 (unnumbered convergence assertion): `m^(n)` converges setwise
to Lebesgue measure on `[0,1]` as `n → ∞`. Lean index `k` is paper `n=k+1`. -/
theorem dyadic_setwise :
    SetwiseConverges
      (fun k : ℕ => dyadicLaw ⟨k + 1, by omega⟩)
      (volume : Measure Observation) := by sorry

end FeinbergPOMDP.Setwise
