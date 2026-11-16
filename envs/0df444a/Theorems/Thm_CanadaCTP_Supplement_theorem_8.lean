-- Prove2me | Theorems.Thm_CanadaCTP_Supplement_theorem_8
-- name    : CanadaCTP.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:40:43.82922+00:00
-- url     : https://prove2.me/theorems/1ea0c6d4-7513-4cc1-81df-0439f933bb93
-- title:
--   Theorem 8 — the competitive ratio $\mathbb E[\mathrm{Opt}]/\mathbb E[\mathrm{Off}]$ is unbounded on two-edge-path graphs
-- statement:
--   The competitive ratio of the Stochastic Canadian Traveller Problem is unbounded, even on disjoint-path graphs where every path has length $2$.
--
--   The competitive ratio is $\sup\mathbb E[\mathrm{Opt}]/\mathbb E[\mathrm{Off}]$ over all inputs, with $0/0=1$, and it is unbounded if $\mathbb E[\mathrm{Off}]=0<\mathbb E[\mathrm{Opt}]$. Precisely: for every constant $C$ there is a CTP instance on a disjoint-path graph whose paths all have two edges with
--   $$C\cdot\mathbb E[\mathrm{Off}]<\mathbb E[\mathrm{Opt}].$$
--
--   This is why the paper measures adaptive policies against the adaptive optimum $\mathbb E[\mathrm{Opt}]$ and not against the offline optimum.
--
--   Differences from the source:
--   - encoding: the competitive ratio sup E[Opt]/E[Off] (0/0 = 1; unbounded if E[Off] = 0 < E[Opt]) is unbounded → ∀ C, ∃ instance I with every path of 2 edges and C·E[Off] < E[Opt]; reason: with the paper's conventions the ratio exceeds C iff C·E[Off] < E[Opt] (E[Opt] is finite)
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Theorem 8, p.31 (Appendix B), with the definition of the competitive ratio on p.31

import Mathlib
import Definitions.Def_CanadaCTP_Supplement_Offline

namespace CanadaCTP.Supplement

open CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
Theorem 8, p.31 (Appendix B): "The competitive ratio of the Stochastic Canadian Traveller Problem
is unbounded, even on disjoint-path graphs, where every path has length 2."

The competitive ratio is `sup E[Opt]/E[Off]` with `0/0 = 1`, and it is unbounded if
`E[Off] = 0 < E[Opt]` (p.31). So: for every constant `C` there is a CTP instance on a disjoint-path
graph whose paths all have two edges with `C · E[Off] < E[Opt]`.

**Formalization Note.** `E[Opt]` is the published `CanadaCTP.optCost`; `E[Off]` is `offCost`, the
expected length of a shortest `s`–`t` path under the realized weights. -/
theorem theorem_8 :
    ∀ C : ℝ, ∃ I : Inst, I.IsCTP ∧ (∀ i, I.m i = 2) ∧
      ENNReal.ofReal C * offCost I < optCost I := by sorry

end CanadaCTP.Supplement
