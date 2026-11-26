-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_InputRAM_bounded_of_valid_body
-- name    : DirectedHamiltonicity.Main.InputRAM.bounded_of_valid_body
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:31:49.991982+00:00
-- url     : https://prove2.me/theorems/95c3dcf4-3d1d-59b6-a26c-06e0e277a9cd
-- title:
--   Lifting a valid-target RAM routine to every encoded graph input
-- statement:
--   Suppose a structured RAM routine realizes the parity estimator on each valid target, with fixed word-width and per-trial work polynomials. On an input graph let $n,m,W$ be the numbers of vertices, arcs and the stated upper weight bound, and let $M$ be its computed trial budget. There are fixed $A,k\in\mathbb N$ such that the compiled program on every signed target and every finite coin tape outputs the corresponding estimator bit at logarithmic cost at most
--
--   $$(M+1)A(n+m+W+1)^k.$$
--
--   The program includes the input reader, target test, graph preprocessing and final halt.
-- source:
--   Auxiliary result for the log-cost RAM formalization of Proposition 4 in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission 811, PDF pp. 5 and 8–11. https://prove2.me/theorems/aa04b14a-8225-48c8-904c-8725ebdcac66

import Definitions.Def_DirectedHamiltonicity_ParityRAMInterfaces

open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM
open TargetedSamplers TargetedSamplers.Structured Multidigraph Classical

theorem DirectedHamiltonicity.Main.InputRAM.bounded_of_valid_body (body : Cmd) (required work : Polynomial ℕ) (run : ValidBodyRuns body required work) :
    ∃ A k : ℕ, BoundedInputRuns (onValid (.seq preprocess body)).program A k := by sorry
