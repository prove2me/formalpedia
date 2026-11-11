-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_lemma_2_5
-- name    : ExactAutobid.Equilibria.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:56:53.187656+00:00
-- url     : https://prove2.me/theorems/78e1b0bb-b4c9-4b18-8cc1-f8ed502bc56e
-- title:
--   Lemma 2.5 — exact generalized circuits with gates C, D, ϕ are FIXP-complete (cited from [FGHLP23])
-- statement:
--   Let a **generalized circuit** have variables $x_0, \dots, x_{N-1} \in [0,1]$, each the output of exactly one gate of the form
--   $$C(x) = 1 - x,\qquad D(x) = \min\{2x, 1\},\qquad \phi(x,y) = \frac{(1+x)(1+y)}{4},$$
--   with cycles and self-inputs allowed. Finding an exact solution (an assignment satisfying every gate equation) is **FIXP-complete under separable linear (SL) reductions**.
--
--   This is the source problem from which all four hardness reductions of the paper start; the paper cites it from Filos-Ratsikas, Giannakopoulos, Hollender, Lazos and Poças (FGHLP23) without proof.
--
--   Differences from the source:
--   - encoding: a generalized circuit with N variables → a list of N ≥ 1 gates CDPhiGate with 0-based input indices below N, binary encoded; solutions x ∈ [0,1]^N with x_i equal to gate i's right-hand side; reason: Lean convention for instances of a real search problem
--   - encoding: polynomial time (binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime on framed binary encodings over the four-letter alphabet Sym, as in the published FixpReciprocal_SLReduces; reason: Lean convention already fixed by the reused FIXP framework; every rational is written in binary
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 6 (PDF 8), Lemma 2.5

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_ExactAutobid_Equilibria_Circuits

open FixpReciprocal

namespace ExactAutobid.Equilibria

/-- **Lemma 2.5 (Exact Generalized Circuits, [FGHLP23]).** Finding an exact solution of a
generalized circuit with gate functions `C(x) = 1 − x`, `D(x) = min{2x, 1}`,
`ϕ(x, y) = (1 + x)(1 + y)/4` is FIXP-complete under SL reductions. -/
theorem lemma_2_5 : FIXPComplete cdphiProblem := by sorry

end ExactAutobid.Equilibria
