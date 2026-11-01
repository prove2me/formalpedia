-- Prove2me | Theorems.Thm_BoundEntPPT_distillable_exists_inseparable_compression
-- name    : BoundEntPPT.distillable_exists_inseparable_compression
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:02:05.64299+00:00
-- url     : https://prove2.me/theorems/23b30d55-7abb-4779-94cd-c07603d91865
-- title:
--   p.3 (unnumbered) — a distillable $\varrho$ has two-dimensional projections $P_A,P_B$ with $\varrho'$ of Eq. (9) inseparable
-- statement:
--   Let $\varrho$ be a state (density matrix) on a finite-dimensional $\mathcal H_A\otimes\mathcal H_B$ that is distillable in the sense of `IsDistillable`. Then there are $N$ and two-dimensional orthogonal projectors $P_A$ on $\mathcal H_A^{\otimes N}$ and $P_B$ on $\mathcal H_B^{\otimes N}$ such that
--
--   $$
--   \varrho'=(P_A\otimes P_B)\,\varrho^{\otimes N}\,(P_A\otimes P_B)
--   $$
--
--   is not separable.
--
--   This is the necessity half of the paper's characterization of distillability (p.3): "if a state $\varrho$ is distillable then there exist two-dimensional projections $P_A$ and $P_B$ so that the state $\varrho'$ given by eq. (9) is inseparable." It combines the three preceding steps (finite $N$, one Kraus pair, compression).
--
--   **Formalization Note** A state is the published `IsDensityMatrix` (positive semidefinite, trace one). $\varrho^{\otimes N}$ is `Information100.P04.copies ρ N` (Alice's factors first). A two-dimensional projection is a Hermitian idempotent matrix of rank exactly $2$. Separability is the published cone `QAlgorithms.Entanglement.IsSeparablePositive`.
--
--   Differences from the source:
--   - reading: ϱ distillable: Alice and Bob obtain pure singlet pairs for N tending to infinity, succeeding with some heralded probability (pp.1–2) → IsDistillable ρ: for every ε > 0 some N and a finite Eq. (4) family give an unnormalized output σ with Tr σ > 0 and ⟨Ψ⁻|σ|Ψ⁻⟩ ≥ (1 − ε) Tr σ; reason: the paper defines distillability only in words; this is the quantitative form of 'outputs arbitrarily close to the singlet with nonzero success probability'
--   - generalization: a protocol producing singlet pairs → one two-qubit output pair suffices; reason: keeping one pair of a k-pair output and discarding the others (Kraus operators ⟨j| ⊗ 1) is again an operation of form (4), so every multi-pair protocol yields a one-pair one; the hypothesis is weaker
--   - generalization: LOCC distillation protocols, written as the operations of Eq. (4) ('the most general operation … [19]') → every finite family (A_i, B_i) of operators into C², with no trace-non-increasing constraint Σ A_i†A_i ⊗ B_i†B_i ≤ 1; reason: the class contains every LOCC protocol and every operation of Eq. (4); a larger class makes the hypothesis weaker
--   - encoding: normalized output (1/M) Σ_i A_i ⊗ B_i ϱ^{⊗N} A_i† ⊗ B_i† and separability with Σ p_i = 1 (Eqs. (2), (4)) → unnormalized output (Eq. (5)) and the separable cone IsSeparablePositive (Eq. (2) without Σ p_i = 1); the fidelity condition is multiplied by M = Tr σ > 0; reason: p.2: 'we will use unnormalized states, as the property of separability as well as satisfying the Peres criterion do not depend on the positive factor'
--   - encoding: two-dimensional projectors P_A, P_B → P Hermitian, P * P = P and P.rank = 2; reason: the definition of a rank-2 orthogonal projector
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.3 (unnumbered, 'Indeed, as shown above, if a state ϱ is distillable then there exist two-dimensional projections')

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_BoundEntPPT_IsDistillable
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.3 (unnumbered, necessity half of the characterization): "Indeed, as shown above,
if a state ϱ is distillable then there exist two-dimensional projections P_A and P_B so that the
state ϱ′ given by eq. (9) is inseparable."

For a distillable state `ρ` there are `N` and two-dimensional orthogonal projectors `P_A` on
`H_A^{⊗N}` and `P_B` on `H_B^{⊗N}` such that `ϱ′ = (P_A ⊗ P_B) ϱ^{⊗N} (P_A ⊗ P_B)` is not
separable.

**Formalization Note.** A state is a published `IsDensityMatrix` (PSD, trace 1; p.4,
footnote [8]). `ϱ^{⊗N}` is `Information100.P04.copies ρ N` (Alice's factors first). A
"two-dimensional projection" is Hermitian, idempotent and of rank exactly 2. Separability is the
published cone `Entanglement.IsSeparablePositive`. Reading of "distillable": `IsDistillable`. -/
theorem distillable_exists_inseparable_compression {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (ρ : Matrix (I × J) (I × J) ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hD : IsDistillable ρ) :
    ∃ N : ℕ, ∃ PA : Matrix (Fin N → I) (Fin N → I) ℂ, ∃ PB : Matrix (Fin N → J) (Fin N → J) ℂ,
      (PA.IsHermitian ∧ PA * PA = PA ∧ PA.rank = 2) ∧
      (PB.IsHermitian ∧ PB * PB = PB ∧ PB.rank = 2) ∧
      ¬ QAlgorithms.Entanglement.IsSeparablePositive
        (Matrix.kronecker PA PB *
          QAlgorithms.Papers.Independent.Information100.P04.copies ρ N *
          Matrix.kronecker PA PB) := by sorry

end BoundEntPPT
