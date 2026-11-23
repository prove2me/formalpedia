-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_compile_flow_oracle
-- name    : ChenCapacityTerminals.Exact.compile_flow_oracle
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T05:40:46.317987+00:00
-- url     : https://prove2.me/theorems/d209ac54-a182-4f3b-bdb4-d1477705d5ab
-- title:
--   Substitute almost-linear integer flow into the headline oracle reduction
-- statement:
--   Let $P$ be a deterministic fixed-pair oracle reduction satisfying all headline volume, outside-work, call-count, per-call-size, and exact-shore guarantees. Let $S$ be an ordinary scalar implementation of the integral flow-and-shore primitive with almost-linear local running time and polylogarithmic dependence on the common numerical scale.
--
--   Then substitution of $S$ for every flow instruction of $P$ yields one ordinary scalar program with the unconditional headline running time: for each fixed polynomial input/capacity class and each $\varepsilon>0$, its time is at most
--   $$
--   C\left((m+n)^{1+\varepsilon}\sqrt n+
--     \widetilde O(m_{\rm in}+n)\right),
--   $$
--   and it returns an exact rooted or global optimal shore in the same execution.
--
--   The compilation copies the actual query and response arc lists, preserves the output shore, and replaces the reduction’s volume bound by a sum of solver costs. The total submitted volume $\widetilde O(M\sqrt n)$ therefore becomes the claimed almost-linear-times-$\sqrt n$ running time, with raw preprocessing retained.
-- source:
--   Thomas Y. Chen, STOC 2027 submission #665, proof of Theorem 1.1, paper p.9 (PDF p.10), final paragraph: substitution and summation over Eq. (6); external solver: van den Brand et al., FOCS 2023, Theorem 1.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=10

import Definitions.Def_ChenCapacityTerminals_Exact_FlowCompilation

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.compile_flow_oracle
    (P : ChenCapacityTerminals.Exact.WordProgram)
    (S : List TrulySubcubicAPSP.Instr)
    (hP : ChenCapacityTerminals.Exact.HeadlineReduction P)
    (hS : ChenCapacityTerminals.Exact.FastWordFlow S) :
    ∃ T : List TrulySubcubicAPSP.Instr,
      ChenCapacityTerminals.Exact.HeadlineTime T := by sorry
