-- Prove2me | Theorems.Thm_DHRUniq_traceNorm_partialTrace_le
-- name    : DHRUniq.traceNorm_partialTrace_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:32:59.886896+00:00
-- url     : https://prove2.me/theorems/80760da8-8884-43fe-ae24-59c730c2ce49
-- title:
--   §7, fact (ii): the partial trace does not increase trace distance
-- statement:
--   Let $\sigma$ and $\varrho$ be states on $\mathcal H^A\otimes\mathcal H^B$, with reduced density operators $\sigma_A=\operatorname{tr}_{\mathcal H^B}\sigma$ and $\varrho_A=\operatorname{tr}_{\mathcal H^B}\varrho$. Then
--
--   $$
--   \|\sigma_A-\varrho_A\|_1\le\|\sigma-\varrho\|_1.
--   $$
--
--   With the Fannes inequality, it gives the asymptotic continuity of the entropy of a reduced state.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces H^A, H^B → ℂ^a, ℂ^b for finite index types a, b with the standard basis; reason: every finite-dimensional Hilbert space is unitarily isomorphic to such a space
--   - encoding: σ_A and ϱ_A are the reduced density operators of ϱ and σ respectively → σ_A reduces σ and ϱ_A reduces ϱ; reason: the printed order swaps the labels; the inequality is symmetric in the two states, so nothing changes
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §7, fact (ii), p. 17

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_partialTrace

open WildeQIT (IsDensityOperator)
open WildeQIT (traceNorm partialTraceRight)

namespace DHRUniq

/-- **The partial trace does not increase the trace norm on states** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §7, fact (ii), p. 17):
`‖σ_A − ϱ_A‖_1 ≤ ‖σ − ϱ‖_1`, where `σ_A`, `ϱ_A` are the reduced density operators.

**Formalization Note** `ϱ_A := tr_{H^B} ϱ` (p. 16) is `partialTraceRight`. The printed "of `ϱ` and `σ`
respectively" swaps the two labels; `σ_A` is the reduction of `σ`. -/
theorem traceNorm_partialTrace_le {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (σ ρ : Matrix (a × b) (a × b) ℂ)
    (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ) :
    traceNorm (partialTraceRight σ - partialTraceRight ρ) ≤ traceNorm (σ - ρ) := by sorry

end DHRUniq
