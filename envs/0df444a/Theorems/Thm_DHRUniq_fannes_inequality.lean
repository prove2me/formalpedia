-- Prove2me | Theorems.Thm_DHRUniq_fannes_inequality
-- name    : DHRUniq.fannes_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:11.461005+00:00
-- url     : https://prove2.me/theorems/0b6ea8e5-28b3-4d73-93d9-34f774670ece
-- title:
--   §7, fact (i), Eq. (31): Fannes inequality
-- statement:
--   Let $\sigma$ and $\varrho$ be states on a finite-dimensional Hilbert space $\mathcal H$ with $\|\sigma-\varrho\|_1\le\tfrac13$. Then
--
--   $$
--   |S(\sigma)-S(\varrho)|\le\|\sigma-\varrho\|_1\log_2\dim\mathcal H+\eta(\|\sigma-\varrho\|_1),
--   $$
--
--   where $\eta(s)=-s\log s$ and $S$ is the von Neumann entropy in bits.
--
--   This is the continuity estimate from which the reduced von Neumann entropy obtains (P3).
--
--   Differences from the source:
--   - reading: η(s) ≡ −s log s, base of the logarithm not printed → η(s) = −s ln s (Real.negMulLog); reason: the natural logarithm gives the smaller right-hand side, so this statement implies the one with log_2; it is the stronger of the two readings
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §7, fact (i), Eq. (31), p. 16

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_QMemory_vonNeumann

open WildeQIT (IsDensityOperator)
open WildeQIT (traceNorm)
open WildeQIT.QMemory (vonNeumann)

namespace DHRUniq

/-- **Fannes inequality** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §7, fact (i), Eq. (31), p. 16):
`|S(σ) − S(ϱ)| ≤ ‖σ − ϱ‖_1 log_2 dim H + η(‖σ − ϱ‖_1)`, for any two states `σ`, `ϱ` on `H` with
`‖σ − ϱ‖_1 ≤ 1/3`; here `η(s) ≡ −s log s`.

**Formalization Note** `S` is in bits (eq. (2)). The base of `log` in `η` is not printed. Natural
logarithm is used (`Real.negMulLog`): it gives the smaller right-hand side, so this statement implies
the one with `log_2`. -/
theorem fannes_inequality {n : Type} [Fintype n] [DecidableEq n] (σ ρ : Matrix n n ℂ)
    (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ) (hclose : traceNorm (σ - ρ) ≤ 1 / 3) :
    |vonNeumann σ - vonNeumann ρ| ≤
      traceNorm (σ - ρ) * Real.logb 2 (Fintype.card n) + Real.negMulLog (traceNorm (σ - ρ)) := by sorry

end DHRUniq
