-- Prove2me | Theorems.Thm_BindingEntChannels_isDistillable_of_copies
-- name    : BindingEntChannels.isDistillable_of_copies
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:00.368225+00:00
-- url     : https://prove2.me/theorems/51cd01d1-cbfa-4c55-ab6f-a7f31ab0cc83
-- title:
--   §II, p. 2 — if $\rho^{\otimes N}$ is FE then $\rho$ is FE
-- statement:
--   Let $\rho$ be an operator on $\mathbb C^I\otimes\mathbb C^J$ and $N\in\mathbb N$. If $\rho^{\otimes N}$ (Alice's $N$ factors grouped first) is distillable, then $\rho$ is distillable.
--
--   The paper applies this to $\rho=(I\otimes\Lambda)P^m_+$: free entanglement of $\big((I\otimes\Lambda)P^m_+\big)^{\otimes N}$ forces free entanglement of $(I\otimes\Lambda)P^m_+$.
--
--   Differences from the source:
--   - generalization: ρ = (I_m ⊗ Λ)P^m_+ and N ≥ 1 → every bipartite operator ρ and every N ∈ ℕ; reason: at N = 0, ρ^{⊗0} is a 1 × 1 product state, which is not distillable, so the implication holds vacuously; the paper's ρ is a case
--   - reading: FE (free entanglement) and BE (bound entanglement) → FE = distillable (definition of ref. [3]); BE = density matrix, not separable, not distillable; reason: p. 1: FE "can be converted into pure singlet form", BE "cannot be distilled"; p. 2: a non-BE state "can be separable or FE"
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem: "we obtain that also (I_m ⊗ Λ^n_m)P^m_+ must be FE")

import Mathlib
import Definitions.Def_BoundEntPPT_IsDistillable

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (proof of the Theorem): from `((I_m ⊗ Λ^n_m)P^m_+)^{⊗N}` being FE, "we obtain that also
(I_m ⊗ Λ^n_m)P^m_+ must be FE".

For every operator `ρ` on `I × J` and every `N`: if `ρ^{⊗N}` is distillable, then `ρ` is
distillable.

**Formalization Note.** Stated for every bipartite `ρ` (the paper applies it to
`(I ⊗ Λ)P^m_+`). At `N = 0`, `ρ^{⊗0}` is the `1 × 1` product state `1`, which is not
distillable, so the statement holds there without a hypothesis `0 < N`. -/
theorem isDistillable_of_copies {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (ρ : Matrix (I × J) (I × J) ℂ) (N : ℕ)
    (h : BoundEntPPT.IsDistillable (QAlgorithms.Papers.Independent.Information100.P04.copies ρ N)) :
    BoundEntPPT.IsDistillable ρ := by sorry

end BindingEntChannels
