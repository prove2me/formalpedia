-- Prove2me | Theorems.Thm_BaconThesis_Collective_eq_8_32
-- name    : BaconThesis.Collective.eq_8_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:08.828752+00:00
-- url     : https://prove2.me/theorems/2fb5e0f1-9dae-4f71-99c8-7cdc9346b605
-- title:
--   Eq. (8.32) — the collective operators satisfy the $\mathfrak{su}(2)$ commutation relations
-- statement:
--   Let $S_x,S_y,S_z$ be the collective operators $S_\alpha=\sum_{i=1}^n\tfrac12\sigma_\alpha^{(i)}$ on $n$ qubits. They satisfy the commutation relations of $\mathfrak{su}(2)$: for all $\alpha,\beta\in\{x,y,z\}$,
--   $$
--   [S_\alpha,S_\beta]=S_\alpha S_\beta-S_\beta S_\alpha=\sum_{\gamma\in\{x,y,z\}} i\,\varepsilon_{\alpha\beta\gamma}\,S_\gamma ,
--   $$
--   with $\varepsilon$ the Levi-Civita symbol; for example $[S_x,S_y]=iS_z$.
--
--   So the collective operators form a representation of $\mathfrak{su}(2)$, which is what makes the angular momentum analysis of §8.6 apply.
--
--   Differences from the source:
--   - encoding: α, β, γ ∈ {x, y, z} → the published labels BBPSSW.Distill.Axis (.x, .y, .z); reason: Lean labels; same instances
--   - encoding: [S_α, S_β] = iε_{α,β,γ} S_γ (repeated γ) → the sum over γ written out; reason: summation convention; same identity
--   - generalization: n qubits, n ≥ 1 (the book starts at n = 1, (8.44)) → every n ∈ ℕ, including n = 0; reason: at n = 0 the space is one-dimensional and every collective operator is 0, where the statement also holds; for n ≥ 1 it is the book's statement
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.32), §8.4, p.114 (PDF p.131)

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit
import Definitions.Def_BaconThesis_Collective_collS
import Definitions.Def_BaconThesis_Collective_levi

open scoped Matrix

namespace BaconThesis.Collective

/-- **(8.32): the collective operators satisfy the `su(2)` commutation relations.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §8.4, (8.32), p.114 (PDF p.131): "These operators form a representation of the Lie algebra
su(2), meaning they satisfy the commutation relations `[S_α, S_β] = i ε_{α,β,γ} S_γ`,
`α, β, γ ∈ {x, y, z}`."

For every number of qubits `n` and all `α, β ∈ {x, y, z}`,
`S_α^[n] S_β^[n] − S_β^[n] S_α^[n] = Σ_γ i ε_{αβγ} S_γ^[n]` (summation over `γ`).

**Formalization Note.** `x, y, z` are `.x, .y, .z : BBPSSW.Distill.Axis`; `ε` is `levi`. The repeated index `γ` is summed,
which is the meaning of the book's formula. -/
theorem eq_8_32 (n : ℕ) (α β : BBPSSW.Distill.Axis) :
    collS n α * collS n β - collS n β * collS n α =
      ∑ γ : BBPSSW.Distill.Axis, (Complex.I * (levi α β γ : ℂ)) • collS n γ := by sorry

end BaconThesis.Collective
