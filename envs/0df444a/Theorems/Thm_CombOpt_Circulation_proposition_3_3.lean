-- Prove2me | Theorems.Thm_CombOpt_Circulation_proposition_3_3
-- name    : CombOpt.Circulation.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:07.4823+00:00
-- url     : https://prove2.me/theorems/ad06e597-3a48-4bcf-9cae-f49083105865
-- title:
--   Proposition 3.3 — flow across a cut
-- statement:
--   Let $x$ be an $(r,s)$-flow in a digraph and let $\delta(R)$ be an $(r,s)$-cut, so $r\in R$ and $s\notin R$. Then
--
--   $$
--   x(\delta(R))-x(\delta(\bar R))=f_x(s),
--   $$
--
--   where $x(A)=\sum_{e\in A}x_e$. The net flow across any cut therefore equals the value of the flow.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 3.3, p. 40

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_delta
import Definitions.Def_CombOpt_Circulation_excess
import Definitions.Def_CombOpt_Circulation_IsFlow

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **Proposition 3.3**, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), p. 40 (PDF p. 49): for any `(r, s)`-cut `δ(R)` and any
`(r, s)`-flow `x`, `x(δ(R)) − x(δ(R̄)) = f_x(s)`.

**Formalization Note** `δ(R)` is an `(r, s)`-cut when `r ∈ R`, `s ∉ R`; `x(A)` is `∑ e ∈ A, x e`. -/
theorem proposition_3_3 (G : MultiDigraph V E) {r s : V} {R : Finset V} (hr : r ∈ R) (hs : s ∉ R)
    {x : E → ℝ} (hx : IsFlow G r s x) :
    ∑ e ∈ delta G R, x e - ∑ e ∈ delta G Rᶜ, x e = excess G x s := by sorry

end CombOpt.Circulation
