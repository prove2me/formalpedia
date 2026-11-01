-- Prove2me | Theorems.Thm_BoundEntPPT_localOutput_ppt
-- name    : BoundEntPPT.localOutput_ppt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:00:48.034246+00:00
-- url     : https://prove2.me/theorems/b1e86c49-4c84-44e2-b591-729ca194be3b
-- title:
--   p.2, last paragraph, and footnote [20] — every operation of form (4) preserves positivity of the partial transpose
-- statement:
--   Let $\varrho$ be an operator on $\mathcal H_A\otimes\mathcal H_B$ with $\varrho^{T_B}\succeq0$. Then for every $N$ and every finite family of operators $A_i:\mathcal H_A^{\otimes N}\to\mathcal K$, $B_i:\mathcal H_B^{\otimes N}\to\mathcal L$ into arbitrary finite-dimensional spaces $\mathcal K$, $\mathcal L$, the output
--
--   $$
--   \sigma=\sum_i (A_i\otimes B_i)\,\varrho^{\otimes N}\,(A_i\otimes B_i)^\dagger
--   $$
--
--   satisfies $\sigma^{T_B}\succeq0$. This is the paper's generalization: "any action of the form $\frac1M\sum_i A_i\otimes B_i\varrho^{\otimes N}A_i^\dagger\otimes B_i^\dagger$ producing an arbitrary two-component system (not necessarily $2\times2$ one) preserves positivity of partial transposition." With $\mathcal K=\mathcal L=\mathbb C^2$ it gives the main result directly.
--
--   **Formalization Note** The positive factor $1/M$ is omitted (p.2, unnormalized states). $\varrho^{\otimes N}$ is `Information100.P04.copies ρ N` and $T_B$ is the published `Information100.P04.gamma`. Only $\varrho^{T_B}\succeq0$ is assumed, not $\varrho\succeq0$.
--
--   Differences from the source:
--   - encoding: normalized output (1/M) Σ_i A_i ⊗ B_i ϱ^{⊗N} A_i† ⊗ B_i† → unnormalized σ = localOutput ρ N A B; reason: p.2: positivity of the partial transpose does not depend on the positive factor
--   - generalization: ϱ a state satisfying the Peres criterion → any complex matrix ρ with gamma ρ ⪰ 0; reason: only positivity of ρ^{T_B} is used; it specializes to states
--   - generalization: N pairs (N ≥ 1), operations of form (4) → every N ≥ 0 and every finite family (A_i, B_i) without completeness constraint; reason: a larger class of operations; it specializes to the paper's
--   - encoding: positivity of partial transposition in an arbitrary product basis → gamma … PosSemidef in the computational basis; reason: the basis does not change eigenvalues (p.2)
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.2, last paragraph; p.4, footnote [20]

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_BoundEntPPT_localOutput
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.2, last paragraph, and p.4, footnote [20]: "This means nothing but that any
action of type (4) on ϱ (including collecting N pairs) preserves positivity of partial
transposition. This result can be generalized [20]: any action of the form
1/M Σ_i A_i ⊗ B_i ϱ^{⊗N} A_i† ⊗ B_i† producing an arbitrary two-component system (not
necessarily 2 × 2 one) preserves positivity of partial transposition."

If `ρ^{T_B} ⪰ 0`, then for every `N` and every finite family `(A_i, B_i)` of operators from
`H_A^{⊗N}`, `H_B^{⊗N}` into arbitrary finite-dimensional `K`, `L`, the output
`σ = Σ_i (A_i ⊗ B_i) ρ^{⊗N} (A_i ⊗ B_i)†` has `σ^{T_B} ⪰ 0`.

**Formalization Note.** The factor `1/M` is omitted (p.2, unnormalized states; a positive factor
does not affect positivity). `T_B` is the published `Information100.P04.gamma`; `ρ^{⊗N}` is
`Information100.P04.copies ρ N`. Only `ρ^{T_B} ⪰ 0` is assumed, not `ρ ⪰ 0` (a generalization);
`N = 0` is allowed (then `ρ^{⊗0}` is the 1 × 1 identity and the claim still holds). -/
theorem localOutput_ppt {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [DecidableEq I] [DecidableEq J] (ρ : Matrix (I × J) (I × J) ℂ)
    (hT : (QAlgorithms.Papers.Independent.Information100.P04.gamma ρ).PosSemidef)
    (N : ℕ) {m : ℕ} (A : Fin m → Matrix K (Fin N → I) ℂ) (B : Fin m → Matrix L (Fin N → J) ℂ) :
    (QAlgorithms.Papers.Independent.Information100.P04.gamma
      (localOutput ρ N A B)).PosSemidef := by sorry

end BoundEntPPT
