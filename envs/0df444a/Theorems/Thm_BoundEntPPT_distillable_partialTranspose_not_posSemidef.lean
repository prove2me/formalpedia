-- Prove2me | Theorems.Thm_BoundEntPPT_distillable_partialTranspose_not_posSemidef
-- name    : BoundEntPPT.distillable_partialTranspose_not_posSemidef
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:02:06.642991+00:00
-- url     : https://prove2.me/theorems/d25001c3-ebaa-446b-993f-0fcbb3d20e4e
-- title:
--   Unnumbered main result, p.3 — every distillable state has a partial transpose that is not positive semidefinite (PPT states are undistillable)
-- statement:
--   Let $\varrho$ be a state (density matrix) on a finite-dimensional bipartite space $\mathcal H_A\otimes\mathcal H_B$. Suppose $\varrho$ is **distillable**: for every $\varepsilon>0$ there are $N$ and finitely many operators $A_i:\mathcal H_A^{\otimes N}\to\mathbb C^2$, $B_i:\mathcal H_B^{\otimes N}\to\mathbb C^2$ such that the unnormalized output
--
--   $$
--   \sigma=\sum_i (A_i\otimes B_i)\,\varrho^{\otimes N}\,(A_i\otimes B_i)^\dagger
--   $$
--
--   has positive success probability $\operatorname{Tr}\sigma>0$ and singlet fidelity $\langle\Psi_-|\sigma|\Psi_-\rangle\ge(1-\varepsilon)\operatorname{Tr}\sigma$, where $\Psi_-=\tfrac1{\sqrt2}(|01\rangle-|10\rangle)$. Then $\varrho$ violates the Peres criterion:
--
--   $$
--   \varrho^{T_B}\not\succeq0,
--   $$
--
--   i.e. the partial transpose $\varrho^{T_B}_{m\mu,n\nu}=\varrho_{m\nu,n\mu}$ has a negative eigenvalue. Equivalently, a state with positive partial transpose cannot be distilled.
--
--   Combined with the existence of inseparable states with positive partial transpose [18], this shows that there are entangled states from which no singlets can be distilled ("bound" entanglement).
--
--   **Formalization Note** A state is the published `IsDensityMatrix`; $\varrho^{T_B}$ is the published `Information100.P04.gamma` (computational product basis); $|\Psi_-\rangle\langle\Psi_-|$ is the published `Dependency50.P42.singletState`. The operations are those of Eq. (4), which contain all LOCC protocols; requiring only one output pair, any positive success probability and no completeness constraint makes the hypothesis weaker and the theorem stronger.
--
--   Differences from the source:
--   - reading: ϱ distillable: Alice and Bob obtain pure singlet pairs for N tending to infinity, succeeding with some heralded probability (pp.1–2) → IsDistillable ρ: for every ε > 0 some N and a finite Eq. (4) family give an unnormalized output σ with Tr σ > 0 and ⟨Ψ⁻|σ|Ψ⁻⟩ ≥ (1 − ε) Tr σ; reason: the paper defines distillability only in words; this is the quantitative form of 'outputs arbitrarily close to the singlet with nonzero success probability'
--   - generalization: a protocol producing singlet pairs → one two-qubit output pair suffices; reason: keeping one pair of a k-pair output and discarding the others (Kraus operators ⟨j| ⊗ 1) is again an operation of form (4), so every multi-pair protocol yields a one-pair one; the hypothesis is weaker
--   - generalization: LOCC distillation protocols, written as the operations of Eq. (4) ('the most general operation … [19]') → every finite family (A_i, B_i) of operators into C², with no trace-non-increasing constraint Σ A_i†A_i ⊗ B_i†B_i ≤ 1; reason: the class contains every LOCC protocol and every operation of Eq. (4); a larger class makes the hypothesis weaker
--   - encoding: normalized output (1/M) Σ_i A_i ⊗ B_i ϱ^{⊗N} A_i† ⊗ B_i† and separability with Σ p_i = 1 (Eqs. (2), (4)) → unnormalized output (Eq. (5)) and the separable cone IsSeparablePositive (Eq. (2) without Σ p_i = 1); the fidelity condition is multiplied by M = Tr σ > 0; reason: p.2: 'we will use unnormalized states, as the property of separability as well as satisfying the Peres criterion do not depend on the positive factor'
--   - encoding: ϱ^{T_B} in an arbitrary product basis; 'violates the criterion' = ϱ^{T_B} has a negative eigenvalue → gamma ρ in the computational product basis; ¬ PosSemidef; reason: p.2: the matrix depends on the basis but its eigenvalues do not; for the Hermitian ϱ^{T_B}, not PSD is equivalent to a negative eigenvalue
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.3 (unnumbered main result: 'Thus we showed that if a state ϱ is distillable, it must violate the Peres separability criterion'); abstract p.1; proof p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_BoundEntPPT_IsDistillable
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.3 (unnumbered main result; abstract p.1, proof p.2): "Thus we showed that if a
state ϱ is distillable, it must violate the Peres separability criterion." Abstract: "It is shown
that if a mixed state can be distilled to the singlet form, it must violate partial
transposition criterion [A. Peres, Phys. Rev. Lett. 76, 1413 (1996)]."

Every distillable state `ρ` on a finite-dimensional `H_A ⊗ H_B` has a partial transpose
`ρ^{T_B}` that is not positive semidefinite. Equivalently, states with positive partial
transpose cannot be distilled.

**Formalization Note.** A state is a published `IsDensityMatrix` (PSD, trace 1; p.4,
footnote [8]) on `I × J` for arbitrary finite `I`, `J`. `T_B` is the published
`Information100.P04.gamma` (Eq. (3), second factor, computational product basis; p.2: "its
eigenvalues do not" depend on the basis). "Violates the criterion" (a negative eigenvalue) is
`¬ PosSemidef`, equivalent for the Hermitian `ρ^{T_B}`. Reading of "distillable":
`IsDistillable` — for every `ε > 0` some `N` and one finite family of Eq. (4) operations into
`C² ⊗ C²` give an output of positive trace (success probability) and singlet fidelity at least
`1 − ε`; one pair, the class of Eq. (4) (which contains LOCC) and no completeness constraint
make the hypothesis weaker and the theorem stronger. -/
theorem distillable_partialTranspose_not_posSemidef {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (ρ : Matrix (I × J) (I × J) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (hD : IsDistillable ρ) :
    ¬ (QAlgorithms.Papers.Independent.Information100.P04.gamma ρ).PosSemidef := by sorry

end BoundEntPPT
