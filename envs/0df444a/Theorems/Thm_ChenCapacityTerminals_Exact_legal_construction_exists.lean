-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_legal_construction_exists
-- name    : ChenCapacityTerminals.Exact.legal_construction_exists
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T06:21:31.695508+00:00
-- url     : https://prove2.me/theorems/af2519df-65bc-4c77-829d-3c58e2f3ff93
-- title:
--   Theorem 2.1 — existence of the legal terminal construction
-- statement:
--   For a prepared rooted network $G$ with $n$ vertices, let $1\le d\le n$, let $L>0$ be rational, and let $t\ge1$. For every nonnegative integer mass function $b$, there is a complete construction record obeying the recipe of Sections 2.1–2.3: repeated single-tail SCC merges until the first stopping test, inherited representatives and heavy-child join trees, sorted external-tail lists and a greedy common cover, incoming edges for final nonsources, and the strict retained-mass postorder rule.
--
--   $$
--   \exists c,\qquad c\text{ is a legal construction for }(G,r,d,L,b,t).
--   $$
--
--   This isolates the finite structural existence part of Theorem 2.1 from its cardinality, expansion, and implementation guarantees. It includes arbitrary legal tie choices and makes no assertion that $L$ is a correct lower bound on the rooted minimum cut.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), Theorem 2.1 and §§2.1–2.3, pp. 3–5, PDF pp. 4–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=4

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem ChenCapacityTerminals.Exact.legal_construction_exists
    (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (hG : Prepared G r) (hd : 1 ≤ d) (hdn : d ≤ G.vertices.card)
    (hL : 0 < L) (ht : 1 ≤ t) : ∃ c, LegalConstruction G r d L b t c := by sorry
