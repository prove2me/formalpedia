-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_terminal_machine_realization
-- name    : ChenCapacityTerminals.Exact.terminal_machine_realization
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T06:22:56.181661+00:00
-- url     : https://prove2.me/theorems/0e7546f9-5fd9-47c6-9f68-d01a3df0139e
-- title:
--   Theorem 2.1 — bounded-word implementation of terminal construction
-- statement:
--   There is one ordinary deterministic bounded-word program that implements the complete legal terminal construction of Theorem 2.1. For every fixed polynomial input/capacity class and polynomial bounds on $t$, the total mass, and the numerator and denominator of $L$, it runs in
--
--   $$
--   \widetilde O\bigl(d(n+m)\bigr)
--   $$
--
--   time and writes an exact legal terminal indicator vector. Its execution also supplies a legal construction record, including SCC partitions, merge-forest witnesses, sorted tail groups, greedy choices, final guide edges, and retained masses.
--
--   The input scan, sorting and summation of single-tail records, SCC searches, selected child outtrees, heap-based greedy cover, and postorder traversal are all charged to this bound. The program precedes the instance and the guarantee holds even when the guessed scale $L$ is wrong.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), Theorem 2.1 and §2.3 “Weighted separation and implementation”, final implementation paragraph, pp. 3–5, PDF pp. 4–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=7

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem ChenCapacityTerminals.Exact.terminal_machine_realization :
    ∃ P : List TrulySubcubicAPSP.Instr, TerminalTime P := by sorry
