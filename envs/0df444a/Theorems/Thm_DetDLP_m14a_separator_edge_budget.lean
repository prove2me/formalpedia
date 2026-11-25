-- Prove2me | Theorems.Thm_DetDLP_m14a_separator_edge_budget
-- name    : DetDLP.m14a_separator_edge_budget
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T01:40:36.063078+00:00
-- url     : https://prove2.me/theorems/3899c7e6-3eb7-4157-97d2-a99e6fb6c438
-- title:
--   Core and total edge budgets for a lookup separator
-- statement:
--   Distinct terminal subdivision vertices each retain an internal port after removing the lookup vertices. Their count is therefore at most twice the internal-edge budget. Including lookup edges, the entire graph has at most three times the internal-edge budget. The estimates allow arbitrary isolated vertices.
-- source:
--   Liu, Zhang and Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Section 4.2(3), Theorem 4.3 (small-scale edge-count bound).

import Theorems.Thm_DetDLP_lookup_separator_core_contraction

open Finset DetDLP
set_option autoImplicit false

theorem DetDLP.m14a_separator_edge_budget {G : BipartiteMultigraph} {m k S D : ℕ}
    (s : LookupSeparatorSpec G m k S D) : 4*m*k ≤ 2*S ∧ G.nE ≤ 3*S := by sorry
