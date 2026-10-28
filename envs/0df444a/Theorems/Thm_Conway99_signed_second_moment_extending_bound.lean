-- Prove2me | Theorems.Thm_Conway99_signed_second_moment_extending_bound
-- name    : Conway99.signed_second_moment_extending_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-27T18:30:49.987313+00:00
-- url     : https://prove2.me/theorems/90407576-12cf-427f-858a-534efd391826
-- title:
--   Quantitative extending bound: $\ge 3$ for $m=1$, $\ge 2$ for $m=2$
-- statement:
--   Keep the residual moment hypotheses of `Conway99.signed_second_moment_sum_F` with $m\in\{1,2\}$. Partition $R=Z\sqcup W$ with $|Z|=12$ and $|W|=60$. Let $\mathrm{ext}$ be a predicate on vertices. Assume $F_v\ge 0$ for all $v\in Z$ and for all non-extending $v\in W$, and $F_v\ge -36$ for all $v\in W$. Then the exact totals $\sum F\in\{-96,-48\}$ force at least three extending vertices in $W$ when $m=1$, and at least two when $m=2$.
--
--   Context: Conway's 99-graph problem asks whether an $\operatorname{srg}(99,14,1,2)$ exists. For an edge $xy$ with unique common neighbour $z$, the $24$-vertex set $L=(N(x)\cup N(y))\setminus\{x,y,z\}$ induces a disjoint union of $4\mathbb Z$-cycles. The present theorems formalize the signed second-moment arithmetic showing that a union of whole components of size $4$ or $8$ forces a $14$-coclique, under the residual moment identities coming from $A^2=12I-A+2J$.
--
--   Credit: mathematics from Ethan Cheung's research handoff (2026-10-28); hand-checked and Lean formalization by Grok Bot. This is an auxiliary criterion only: it does **not** resolve Conway's 99-graph problem, does **not** claim novelty, does **not** exclude the residual local types $C_{24}$ or $C_{12}\sqcup C_{12}$, and does **not** claim $\alpha(G)\ge 14$ unconditionally. The accompanying certificates Python script verifies fractional models only, not these theorems.
-- source:
--   Mathematics from Ethan Cheung research handoff (2026-10-28); hand-checked and Lean by Grok Bot. Auxiliary edge-local signed second-moment criterion for srg(99,14,1,2). Does NOT solve Conway's 99-graph problem; does NOT claim novelty; does NOT exclude C24 or C12⊔C12; does NOT claim α(G)≥14 unconditionally. Certificates Python verifies fractional models only, not these theorems.

import Mathlib
open Finset

namespace Conway99

theorem signed_second_moment_extending_bound {V : Type*} [DecidableEq V]
    (R Z : Finset V) (m : ℕ) (hm : m = 1 ∨ m = 2) (q s t : V → ℤ)
    (extV : V → Prop) [DecidablePred extV]
    (hZR : Z ⊆ R) (_hZcard : #Z = 12) (hR : #R = 72)
    (hs2 : ∑ v ∈ R, (s v) ^ 2 = (40 : ℤ) * m)
    (ht2 : ∑ v ∈ R, (t v) ^ 2 = (40 : ℤ) * (6 - m))
    (hq : ∑ v ∈ R, q v = (44 : ℤ) * m)
    (hq2 : ∑ v ∈ R, (q v) ^ 2 = (24 : ℤ) * m * (m + 1))
    (hFZ : ∀ v ∈ Z, (0 : ℤ) ≤ 6 * ((q v) - 1) ^ 2 + 6 - 3 * ((s v) ^ 2 + (t v) ^ 2))
    (hFWnon : ∀ v ∈ R \ Z, ¬ extV v →
      (0 : ℤ) ≤ 6 * ((q v) - 1) ^ 2 + 6 - 3 * ((s v) ^ 2 + (t v) ^ 2))
    (hFWlow : ∀ v ∈ R \ Z, (-36 : ℤ) ≤ 6 * ((q v) - 1) ^ 2 + 6 - 3 * ((s v) ^ 2 + (t v) ^ 2)) :
    (m = 1 → 3 ≤ #{v ∈ R \ Z | extV v}) ∧
      (m = 2 → 2 ≤ #{v ∈ R \ Z | extV v}) := by sorry

end Conway99
