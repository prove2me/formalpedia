-- Prove2me | Theorems.Thm_BoundEntPPT_two_qubit_separable_of_ppt
-- name    : BoundEntPPT.two_qubit_separable_of_ppt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:47.454623+00:00
-- url     : https://prove2.me/theorems/6f44df67-3b37-4cf9-99e4-5820b3b97152
-- title:
--   p.2, citing [15] — a two-qubit operator with positive partial transpose is separable
-- statement:
--   Let $X$ be a positive semidefinite operator on $\mathbb C^2\otimes\mathbb C^2$ whose partial transpose $X^{T_B}$ (Eq. (3)) is also positive semidefinite. Then $X$ is separable:
--
--   $$
--   X\succeq0,\ \ X^{T_B}\succeq0\ \Longrightarrow\ X=\sum_j w_j\,\alpha_j\otimes\beta_j,\qquad w_j\ge0,\ \alpha_j,\beta_j\ \text{states on }\mathbb C^2 .
--   $$
--
--   This is the sufficiency of the Peres partial-transposition test for two qubits, proved in [15] (M. Horodecki, P. Horodecki, R. Horodecki, Phys. Lett. A 223, 1 (1996)) and used in the proof of the main result to conclude that the $4\times4$ block $M_{2q}$ of $\varrho'$ cannot have positive partial transpose.
--
--   **Formalization Note** The operator is unnormalized (p.2), so the statement covers $X=0$ and every positive multiple of a two-qubit state. Separability is the published cone `QAlgorithms.Entanglement.IsSeparablePositive`; the partial transpose is the published `Information100.P04.gamma` in the computational basis. The qubit–trit case, also mentioned on p.2, is not part of this item.
--
--   Differences from the source:
--   - encoding: two-qubit state → positive semidefinite X on Fin 2 × Fin 2 (unnormalized), separable in the cone IsSeparablePositive; reason: p.2 uses unnormalized states; separability and PPT do not depend on the positive factor, and X = 0 is separable
--   - encoding: partial transposition in an arbitrary product basis → gamma X in the computational basis; reason: positivity does not depend on the product basis (p.2)
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.2 (citing [15], 'due to the sufficiency of the partial transposition test for two-qubit case [15]')

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.2, citing [15] (M. Horodecki, P. Horodecki, R. Horodecki, Phys. Lett. A 223, 1
(1996)): "If M_{2q} were positive after partial transposition, then, due to the sufficiency of
the partial transposition test for two-qubit case [15], M_{2q} would represent a separable
two-qubit state."

A positive semidefinite operator on `C² ⊗ C²` whose partial transpose (Eq. (3)) is positive
semidefinite is separable.

**Formalization Note.** Unnormalized (p.2, "we will use unnormalized states"): the statement
covers `X = 0` and every positive multiple of a two-qubit state. Separability is the published
cone `Entanglement.IsSeparablePositive` (Eq. (2) without `Σ p_i = 1`); the partial transpose is
the published `Information100.P04.gamma` (second factor, computational basis, Eq. (3)). Only the
two-qubit case is stated; the paper's parenthetical qubit–trit case is a separate cited fact the
proof does not use. -/
theorem two_qubit_separable_of_ppt (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hX : X.PosSemidef)
    (hT : (QAlgorithms.Papers.Independent.Information100.P04.gamma X).PosSemidef) :
    QAlgorithms.Entanglement.IsSeparablePositive X := by sorry

end BoundEntPPT
