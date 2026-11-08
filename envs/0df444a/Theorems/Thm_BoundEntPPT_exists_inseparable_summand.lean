-- Prove2me | Theorems.Thm_BoundEntPPT_exists_inseparable_summand
-- name    : BoundEntPPT.exists_inseparable_summand
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:24:51.443828+00:00
-- url     : https://prove2.me/theorems/b19a296e-0764-4da7-b156-e4df89dfef2d
-- title:
--   p.2, after Eq. (6) — if $\sum_i\varrho_i$ is inseparable, some $\varrho_{i_0}$ is inseparable
-- statement:
--   Let $(X_i)_{i\in\iota}$ be a finite family of operators on $\mathcal H_A\otimes\mathcal H_B$. If the sum
--
--   $$
--   \sum_{i\in\iota} X_i
--   $$
--
--   is not separable, then some summand $X_{i_0}$ is not separable. Equivalently, a finite sum of separable operators is separable: "by summing separable states we cannot get inseparable one".
--
--   In the paper the summands are $\varrho_i=(A_i\otimes B_i)\varrho^{\otimes N}(A_i\otimes B_i)^\dagger$ (Eq. (6)) and the sum is the output $\varrho_{2q}$ of Eq. (5); this reduces the general operation to a single Kraus pair $(A_{i_0},B_{i_0})$.
--
--   **Formalization Note** Separability is the published cone `QAlgorithms.Entanglement.IsSeparablePositive` (unnormalized Eq. (2)).
--
--   Differences from the source:
--   - generalization: the summands ϱ_i = A_i ⊗ B_i ϱ^{⊗N} A_i† ⊗ B_i† of Eq. (6) → an arbitrary finite family of complex matrices X_i on I × J; reason: the argument uses only that the separable cone is closed under finite sums; it specializes to Eq. (6)
--   - encoding: separable (Eq. (2)) for unnormalized operators → QAlgorithms.Entanglement.IsSeparablePositive (finite sums Σ w_j A_j ⊗ B_j, w_j ≥ 0, A_j, B_j density matrices); reason: p.2 drops Σ p_i = 1 for unnormalized states; finite sums suffice in finite dimension (Carathéodory)
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.2, after Eq. (6)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.2, after Eq. (6): "Since ϱ_{2q} is inseparable then at least for some i = i₀ the
state ϱ_{i₀} must be inseparable. Indeed, by summing separable states we cannot get inseparable
one."

If a finite sum of operators on `I × J` is not separable, one of the summands is not separable.

**Formalization Note.** Separability is the published cone `Entanglement.IsSeparablePositive`
(unnormalized Eq. (2)). The summands are arbitrary complex matrices indexed by any finite type;
the paper applies the statement to `ϱ_i = A_i ⊗ B_i ϱ^{⊗N} A_i† ⊗ B_i†` of Eq. (6)
(a generalization). -/
theorem exists_inseparable_summand {ι I J : Type*} [Fintype ι] [Fintype I] [Fintype J]
    (X : ι → Matrix (I × J) (I × J) ℂ)
    (h : ¬ QAlgorithms.Entanglement.IsSeparablePositive (∑ i, X i)) :
    ∃ i, ¬ QAlgorithms.Entanglement.IsSeparablePositive (X i) := by sorry

end BoundEntPPT
