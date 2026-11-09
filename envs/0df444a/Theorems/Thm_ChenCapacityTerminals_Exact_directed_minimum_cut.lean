-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_directed_minimum_cut
-- name    : ChenCapacityTerminals.Exact.directed_minimum_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:37.933736+00:00
-- url     : https://prove2.me/theorems/84640da3-18b4-40b2-af3f-3b362bf9cba8
-- title:
--   Theorem 1.1 — Exact deterministic rooted and global directed minimum cut
-- statement:
--   Let $G$ be a directed graph on $n\ge2$ vertices, with polynomially many raw arc records and nonnegative integer capacities bounded by a fixed polynomial in $n$. Parallel and antiparallel arcs, loops, zeros and arbitrary degrees are allowed. Let $m$ be the number of positive ordered pairs after coalescing parallel arcs and dropping loops, and put $M=m+n$. There is a deterministic bounded-word algorithm returning an exact rooted minimum entering shore for any prescribed root, or an exact global minimum entering shore, in
--   $$M^{1+o(1)}\sqrt n$$
--   time, with an additional $\widetilde O(m_{\rm in}+n)$ for raw preprocessing. This includes zero-valued optima and imposes no reachability or connectivity assumption.
--
--   There is also a deterministic fixed-pair reduction with total submitted-network volume $\widetilde O(M\sqrt n)$ and outside work $\widetilde O(M\sqrt n+m_{\rm in}+n)$. It uses $\widetilde O(\sqrt n)$ calls, each with $O(n)$ vertices and $O(M)$ arcs, and returns the same exact cut types. Its oracle returns an integral flow and a matching shore, with arbitrary valid ties.
--
--   One ordinary program precedes all $\varepsilon>0$ and all instances: for every fixed polynomial input/capacity class and every $\varepsilon>0$, a uniform positive constant bounds its steps by $M^{1+\varepsilon}\sqrt n$ plus the stated preprocessing term. Soft-O constants and logarithm exponents also precede the instances. The almost-linear fixed-pair theorem of van den Brand et al. (FOCS 2023, Theorem 1.1) is an external proof dependency, not a hypothesis of this goal.
--
--   The goal retains all runtime, volume, outside-work and per-call guarantees of the source, in both problem modes.
--
--   Differences from the source:
--   - encoding: finite vertex labels and original arc identities → canonical labels 0,...,n-1 for machine inputs, arbitrary finite natural labels for structural statements, and ordered arc records; reason: finite relabeling preserves every instance; arc positions preserve multiplicities
--   - encoding: m after coalescing, with an additional soft-O raw-input preprocessing cost → supportSize is n plus the positive coalesced loopless support; raw arc-list cost appears separately in outside work and ordinary running time; reason: this preserves the paper’s distinction between graph size and raw input length
--   - encoding: deterministic time M^(1+o(1)) sqrt(n) and a fixed-pair reduction → existence of an ordinary scalar program for unconditional time, and existence of an oracle program for all reduction bounds; reason: both realizers solve both source modes; the headline has no assumed flow primitive and the reduction records actual calls
--   - encoding: O and soft-O resource guarantees → positive constants and logarithm exponents quantified before the instances; actual finite-program executions and network traces; reason: uniform constants replace asymptotic notation without fixing an unsupported numeral or granting free graph operations
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 1, 8–10, PDF p. 2, 9–11, Theorem 1.1 and its proof, Eq. (6), §4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=2, 9–11

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

theorem directed_minimum_cut :
    (∃ P : WordProgram, HeadlineReduction P) ∧
    ∃ P : List TrulySubcubicAPSP.Instr, HeadlineTime P := by sorry

end ChenCapacityTerminals.Exact
