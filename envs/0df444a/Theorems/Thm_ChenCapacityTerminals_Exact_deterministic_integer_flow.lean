-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_deterministic_integer_flow
-- name    : ChenCapacityTerminals.Exact.deterministic_integer_flow
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T05:39:30.663993+00:00
-- url     : https://prove2.me/theorems/8ca31a85-1eb4-4f0e-bd0b-37034e85aca4
-- title:
--   External deterministic almost-linear integral maximum flow on the scalar word RAM
-- statement:
--   There is one deterministic ordinary bounded-word program that computes an integral maximum flow together with a matching minimum sink shore for every valid integral fixed-pair query.
--
--   For every polynomial bound on query size and capacities relative to a common numerical scale $N$, and every $\varepsilon>0$, its charged execution time is uniformly at most
--   $$
--   C\,(n_Q+|E_Q|+2)^{1+\varepsilon}\,(\log N)^{O(1)}.
--   $$
--   The program precedes $\varepsilon$ and the query. The returned shore and the values on all raw arcs are explicit charged output; parallel arcs are indexed by record position.
--
--   This is the external fixed-pair primitive needed by Chen’s final summation argument. It is a conclusion of the cited algorithm, not a hypothesis about the directed-minimum-cut input.
-- source:
--   van den Brand, Chen, Kyng, Liu, Meierhans, Probst Gutenberg, Sachdeva, FOCS 2023, Theorem 1.1, arXiv:2309.16629 p.3 (PDF p.4), https://arxiv.org/pdf/2309.16629#page=4 ; invoked by Thomas Y. Chen, STOC 2027 submission #665, proof of Theorem 1.1, paper p.9 (PDF p.10).

import Definitions.Def_ChenCapacityTerminals_Exact_FlowCompilation

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.deterministic_integer_flow :
    ∃ S : List TrulySubcubicAPSP.Instr,
      ChenCapacityTerminals.Exact.FastWordFlow S := by sorry
