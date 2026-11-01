-- Prove2me | Theorems.Thm_BoundEntPPT_partialTranspose_posSemidef_iff_copies
-- name    : BoundEntPPT.partialTranspose_posSemidef_iff_copies
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:25:14.928442+00:00
-- url     : https://prove2.me/theorems/108e8336-ec34-46e6-af86-f7e67e45aa7c
-- title:
--   p.2, after Eq. (3), citing [14] — $\varrho^{T_B}\succeq0$ if and only if $(\varrho^{\otimes N})^{T_B}\succeq0$
-- statement:
--   Let $\varrho$ be a state (density matrix) on a finite-dimensional $\mathcal H_A\otimes\mathcal H_B$ and $N\ge1$. Then
--
--   $$
--   \varrho^{T_B}\succeq0\quad\Longleftrightarrow\quad(\varrho^{\otimes N})^{T_B}\succeq0,
--   $$
--
--   where $\varrho^{\otimes N}$ is regarded as an operator on $\mathcal H_A^{\otimes N}\otimes\mathcal H_B^{\otimes N}$ and $T_B$ transposes all of Bob's factors. In the paper's words, $\varrho$ violates the criterion if and only if any $N$-fold tensor product $\varrho^{\otimes N}$ does. The main proof uses the direction "$\varrho^{\otimes N}$ violates $\Rightarrow$ $\varrho$ violates".
--
--   **Formalization Note** A state is the published `IsDensityMatrix` (positive semidefinite, trace one); the trace condition is needed for "$\Leftarrow$" (for $H=-1$, $H^{\otimes2}\succeq0$ but $H$ is not). $\varrho^{\otimes N}$ is `Information100.P04.copies ρ N` (Alice's $N$ factors first) and $T_B$ is the published `Information100.P04.gamma`.
--
--   Differences from the source:
--   - encoding: any N-fold tensor product → N ≥ 1; reason: an N-fold product has at least one factor; at N = 0 the right side is the 1 × 1 identity
--   - encoding: ϱ violates the criterion iff ϱ^{⊗N} does (negative eigenvalues) → (gamma ρ).PosSemidef ↔ (gamma (copies ρ N)).PosSemidef, computational basis; reason: the contrapositive form of the same equivalence; for Hermitian matrices not PSD means a negative eigenvalue, and the basis does not change eigenvalues (p.2)
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.2, after Eq. (3) (citing [14]); used after Eq. (10)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.2, after Eq. (3), citing [14]: "In particular, it implies that ϱ violates the
criterion if and only if any N-fold tensor product ϱ^{⊗N} = ϱ ⊗ … ⊗ ϱ does [14]." Used on p.2:
"Thus the state ϱ^{⊗N} violates the partial transposition criterion. However, as it was
mentioned, this implies that also ϱ does."

For a state `ρ` and `N ≥ 1`: `ρ^{T_B} ⪰ 0` if and only if `(ρ^{⊗N})^{T_B} ⪰ 0`.

**Formalization Note.** A state is a published `IsDensityMatrix` (PSD, trace 1). `ρ^{⊗N}` is
`Information100.P04.copies ρ N` on `(Fin N → I) × (Fin N → J)` (Alice's `N` factors first, so
that `T_B` of `ρ^{⊗N}` transposes all of Bob's factors); `T_B` is `Information100.P04.gamma`.
"N-fold" means `N ≥ 1` (at `N = 0` the right side is the 1 × 1 identity). The trace-one
condition is needed for "←": for a Hermitian `H = −1`, `H^{⊗2} ⪰ 0` but `H` is not. -/
theorem partialTranspose_posSemidef_iff_copies {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (ρ : Matrix (I × J) (I × J) ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) (N : ℕ) (hN : 1 ≤ N) :
    (QAlgorithms.Papers.Independent.Information100.P04.gamma ρ).PosSemidef ↔
      (QAlgorithms.Papers.Independent.Information100.P04.gamma
        (QAlgorithms.Papers.Independent.Information100.P04.copies ρ N)).PosSemidef := by sorry

end BoundEntPPT
