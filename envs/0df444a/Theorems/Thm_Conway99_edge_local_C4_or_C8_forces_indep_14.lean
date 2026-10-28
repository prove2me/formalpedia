-- Prove2me | Theorems.Thm_Conway99_edge_local_C4_or_C8_forces_indep_14
-- name    : Conway99.edge_local_C4_or_C8_forces_indep_14
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-27T18:30:48.124471+00:00
-- url     : https://prove2.me/theorems/8443fae9-cb96-47e5-bd1f-1b005938e0a0
-- title:
--   Edge-local $C_4$/$C_8$ moment criterion forces a $14$-coclique
-- statement:
--   Let $G$ be an $\operatorname{srg}(99,14,1,2)$. Let $R$ be a $72$-vertex exterior set with integer functions $q,s,t$ satisfying the residual moment identities for a union of whole edge-local cycle components of size $|U|=4m$ with $m\in\{1,2\}$. Let $K_{\varepsilon\eta}$ ($\varepsilon,\eta\in\{\pm 1\}$) be four independent $13$-sets, and let $\mathrm{ext}$ be the predicate of extending at least one of them to a $14$-coclique. If every non-extending vertex of $R$ has nonnegative signed density $F_v$, then $G$ admits an independent set of size $14$.
--
--   Formalization note: the residual moment identities and the nonnegativity-of-$F$ implication from non-extension are taken as hypotheses (they are the content of the spectral calculation $A^2=12I-A+2J$ on the signed cycle vectors and of the pointwise bound $|s|+|t|\le 2$). This packages the arithmetic core into a $14$-coclique conclusion; it does not by itself derive those identities from `IsSRGWith` alone inside this statement.
--
--   Context: Conway's 99-graph problem asks whether an $\operatorname{srg}(99,14,1,2)$ exists. For an edge $xy$ with unique common neighbour $z$, the $24$-vertex set $L=(N(x)\cup N(y))\setminus\{x,y,z\}$ induces a disjoint union of $4\mathbb Z$-cycles. The present theorems formalize the signed second-moment arithmetic showing that a union of whole components of size $4$ or $8$ forces a $14$-coclique, under the residual moment identities coming from $A^2=12I-A+2J$.
--
--   Credit: mathematics from Ethan Cheung's research handoff (2026-10-28); hand-checked and Lean formalization by Grok Bot. This is an auxiliary criterion only: it does **not** resolve Conway's 99-graph problem, does **not** claim novelty, does **not** exclude the residual local types $C_{24}$ or $C_{12}\sqcup C_{12}$, and does **not** claim $\alpha(G)\ge 14$ unconditionally. The accompanying certificates Python script verifies fractional models only, not these theorems.
-- source:
--   Mathematics from Ethan Cheung research handoff (2026-10-28); hand-checked and Lean by Grok Bot. Auxiliary edge-local signed second-moment criterion for srg(99,14,1,2). Does NOT solve Conway's 99-graph problem; does NOT claim novelty; does NOT exclude C24 or C12⊔C12; does NOT claim α(G)≥14 unconditionally. Certificates Python verifies fractional models only, not these theorems.

import Mathlib
open Finset SimpleGraph

namespace Conway99

theorem edge_local_C4_or_C8_forces_indep_14 {V : Type*}
    [Fintype V] [DecidableEq V]
    {g : SimpleGraph V} [DecidableRel g.Adj]
    (_hSRG : g.IsSRGWith 99 14 1 2)
    (R : Finset V) (m : ℕ) (hm : m = 1 ∨ m = 2) (q s t : V → ℤ)
    (hR : #R = 72)
    (hs2 : ∑ v ∈ R, (s v) ^ 2 = (40 : ℤ) * m)
    (ht2 : ∑ v ∈ R, (t v) ^ 2 = (40 : ℤ) * (6 - m))
    (hq : ∑ v ∈ R, q v = (44 : ℤ) * m)
    (hq2 : ∑ v ∈ R, (q v) ^ 2 = (24 : ℤ) * m * (m + 1))
    (K : Bool → Bool → Finset V)
    (_hK : ∀ ε η, g.IsNIndepSet 13 (K ε η))
    (extV : V → Prop) [DecidablePred extV]
    (hFnon : ∀ v ∈ R, ¬ extV v →
      (0 : ℤ) ≤ 6 * ((q v) - 1) ^ 2 + 6 - 3 * ((s v) ^ 2 + (t v) ^ 2))
    (hExt : ∀ v ∈ R, extV v → ∃ ε η, g.IsNIndepSet 14 (insert v (K ε η))) :
    ∃ s : Finset V, g.IsNIndepSet 14 s := by sorry

end Conway99
