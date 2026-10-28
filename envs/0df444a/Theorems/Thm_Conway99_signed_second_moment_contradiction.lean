-- Prove2me | Theorems.Thm_Conway99_signed_second_moment_contradiction
-- name    : Conway99.signed_second_moment_contradiction
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-27T18:30:49.68218+00:00
-- url     : https://prove2.me/theorems/8e49abb2-7998-4aee-aaa9-d7bf4f69b4bb
-- title:
--   Nonnegative $F$ on $R$ contradicts the $m\in\{1,2\}$ moment identity
-- statement:
--   Under the same residual moment hypotheses as `Conway99.signed_second_moment_sum_F` with $m\in\{1,2\}$, the identity $\sum_{v\in R}F_v=48(3m^2-8m+3)\in\{-96,-48\}$ is strictly negative. Therefore it is impossible that $F_v\ge 0$ for every $v\in R$. In the edge-local analysis, nonnegativity of $F$ on $R$ is the numerical consequence of failing to extend any of the four canonical $13$-cocliques, so some exterior vertex must extend.
--
--   Context: Conway's 99-graph problem asks whether an $\operatorname{srg}(99,14,1,2)$ exists. For an edge $xy$ with unique common neighbour $z$, the $24$-vertex set $L=(N(x)\cup N(y))\setminus\{x,y,z\}$ induces a disjoint union of $4\mathbb Z$-cycles. The present theorems formalize the signed second-moment arithmetic showing that a union of whole components of size $4$ or $8$ forces a $14$-coclique, under the residual moment identities coming from $A^2=12I-A+2J$.
--
--   Credit: mathematics from Ethan Cheung's research handoff (2026-10-28); hand-checked and Lean formalization by Grok Bot. This is an auxiliary criterion only: it does **not** resolve Conway's 99-graph problem, does **not** claim novelty, does **not** exclude the residual local types $C_{24}$ or $C_{12}\sqcup C_{12}$, and does **not** claim $\alpha(G)\ge 14$ unconditionally. The accompanying certificates Python script verifies fractional models only, not these theorems.
-- source:
--   Mathematics from Ethan Cheung research handoff (2026-10-28); hand-checked and Lean by Grok Bot. Auxiliary edge-local signed second-moment criterion for srg(99,14,1,2). Does NOT solve Conway's 99-graph problem; does NOT claim novelty; does NOT exclude C24 or C12⊔C12; does NOT claim α(G)≥14 unconditionally. Certificates Python verifies fractional models only, not these theorems.

import Mathlib
open Finset

namespace Conway99

theorem signed_second_moment_contradiction {V : Type*} [DecidableEq V]
    (R : Finset V) (m : ℕ) (hm : m = 1 ∨ m = 2) (q s t : V → ℤ)
    (hR : #R = 72)
    (hs2 : ∑ v ∈ R, (s v) ^ 2 = (40 : ℤ) * m)
    (ht2 : ∑ v ∈ R, (t v) ^ 2 = (40 : ℤ) * (6 - m))
    (hq : ∑ v ∈ R, q v = (44 : ℤ) * m)
    (hq2 : ∑ v ∈ R, (q v) ^ 2 = (24 : ℤ) * m * (m + 1))
    (hF : ∀ v ∈ R, (0 : ℤ) ≤ 6 * ((q v) - 1) ^ 2 + 6 - 3 * ((s v) ^ 2 + (t v) ^ 2)) :
    False := by sorry

end Conway99
