-- Prove2me | Theorems.Thm_DHRUniq_traceNorm_pureState_sub
-- name    : DHRUniq.traceNorm_pureState_sub
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:49.673057+00:00
-- url     : https://prove2.me/theorems/9c1943a9-49c5-4141-90c4-58005327fd47
-- title:
--   Display (36): trace distance of two pure states
-- statement:
--   Let $\psi$ and $\phi$ be unit vectors of a finite-dimensional Hilbert space and let $\epsilon$ satisfy $|\langle\psi|\phi\rangle|^2\ge1-\epsilon$. Then
--
--   $$
--   \big\||\psi\rangle\langle\psi|-|\phi\rangle\langle\phi|\big\|_1=2\sqrt{1-|\langle\psi|\phi\rangle|^2}\le2\sqrt\epsilon .
--   $$
--
--   In the proof of the uniqueness theorem it shows that the truncated state is close to $|\psi^{\otimes n}\rangle$, so (P3) applies.
--
--   Differences from the source:
--   - generalization: the vectors ψ^⊗n and φ_n, with |⟨ψ^⊗n|φ_n⟩|² ≥ 1 − ε from (35) → any two unit vectors and any ε with |⟨ψ|φ⟩|² ≥ 1 − ε; reason: the display is the instance ψ := ψ^⊗n, φ := φ_n
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §8, display (36), p. 18

import Mathlib
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)
open WildeQIT (traceNorm)

namespace DHRUniq

/-- **Display (36)** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §8, p. 18):
`‖ |ψ^{⊗n}⟩⟨ψ^{⊗n}| − |φ_n⟩⟨φ_n| ‖_1 = 2√(1 − |⟨ψ^{⊗n}|φ_n⟩|²) ≤ 2√ε`.

**Formalization Note** Stated for any two unit vectors `ψ`, `φ` of a finite-dimensional space and any
`ε` with `|⟨ψ|φ⟩|² ≥ 1 − ε`, the hypothesis that (35) gives for `ψ^{⊗n}` and `φ_n`. -/
theorem traceNorm_pureState_sub {ι : Type} [Fintype ι] [DecidableEq ι] (ψ φ : ι → ℂ)
    (hψ : IsUnitVec ψ) (hφ : IsUnitVec φ) (ε : ℝ) (hε : 1 - ε ≤ ‖∑ z, star (ψ z) * φ z‖ ^ 2) :
    traceNorm (pureState ψ - pureState φ) = 2 * Real.sqrt (1 - ‖∑ z, star (ψ z) * φ z‖ ^ 2) ∧
      2 * Real.sqrt (1 - ‖∑ z, star (ψ z) * φ z‖ ^ 2) ≤ 2 * Real.sqrt ε := by sorry

end DHRUniq
