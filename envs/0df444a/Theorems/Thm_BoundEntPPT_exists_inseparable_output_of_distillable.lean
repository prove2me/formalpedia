-- Prove2me | Theorems.Thm_BoundEntPPT_exists_inseparable_output_of_distillable
-- name    : BoundEntPPT.exists_inseparable_output_of_distillable
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:02:01.728289+00:00
-- url     : https://prove2.me/theorems/30108c74-0afb-4815-bec7-08f3835b2487
-- title:
--   p.2 (unnumbered) — a distillable $\varrho$ gives an inseparable two-qubit output for some finite $N$
-- statement:
--   Let $\varrho$ be an operator on a finite-dimensional $\mathcal H_A\otimes\mathcal H_B$ that is distillable: for every $\varepsilon>0$ some $N$ and some finite family of operators $A_i:\mathcal H_A^{\otimes N}\to\mathbb C^2$, $B_i:\mathcal H_B^{\otimes N}\to\mathbb C^2$ give an unnormalized output $\sigma=\sum_i (A_i\otimes B_i)\varrho^{\otimes N}(A_i\otimes B_i)^\dagger$ with $\operatorname{Tr}\sigma>0$ and singlet fidelity $\langle\Psi_-|\sigma|\Psi_-\rangle\ge(1-\varepsilon)\operatorname{Tr}\sigma$. Then there are a finite $N$ and such a family whose output
--
--   $$
--   \sigma=\sum_i (A_i\otimes B_i)\,\varrho^{\otimes N}\,(A_i\otimes B_i)^\dagger
--   $$
--
--   is **not separable**, i.e. not of the form $\sum_j w_j\,\alpha_j\otimes\beta_j$ with $w_j\ge0$ and $\alpha_j,\beta_j$ states.
--
--   This is the first step of the proof of the main result: distillability, an asymptotic property, yields a single inseparable two-qubit pair at a finite number of copies.
--
--   **Formalization Note** Separability is the published cone `QAlgorithms.Entanglement.IsSeparablePositive` (Eq. (2) without $\sum p_i=1$, as p.2 prescribes for unnormalized operators). No property of $\varrho$ is assumed.
--
--   Differences from the source:
--   - reading: ϱ distillable: Alice and Bob obtain pure singlet pairs for N tending to infinity, succeeding with some heralded probability (pp.1–2) → IsDistillable ρ: for every ε > 0 some N and a finite Eq. (4) family give an unnormalized output σ with Tr σ > 0 and ⟨Ψ⁻|σ|Ψ⁻⟩ ≥ (1 − ε) Tr σ; reason: the paper defines distillability only in words; this is the quantitative form of 'outputs arbitrarily close to the singlet with nonzero success probability'
--   - generalization: a protocol producing singlet pairs → one two-qubit output pair suffices; reason: keeping one pair of a k-pair output and discarding the others (Kraus operators ⟨j| ⊗ 1) is again an operation of form (4), so every multi-pair protocol yields a one-pair one; the hypothesis is weaker
--   - generalization: LOCC distillation protocols, written as the operations of Eq. (4) ('the most general operation … [19]') → every finite family (A_i, B_i) of operators into C², with no trace-non-increasing constraint Σ A_i†A_i ⊗ B_i†B_i ≤ 1; reason: the class contains every LOCC protocol and every operation of Eq. (4); a larger class makes the hypothesis weaker
--   - encoding: normalized output (1/M) Σ_i A_i ⊗ B_i ϱ^{⊗N} A_i† ⊗ B_i† and separability with Σ p_i = 1 (Eqs. (2), (4)) → unnormalized output (Eq. (5)) and the separable cone IsSeparablePositive (Eq. (2) without Σ p_i = 1); the fidelity condition is multiplied by M = Tr σ > 0; reason: p.2: 'we will use unnormalized states, as the property of separability as well as satisfying the Peres criterion do not depend on the positive factor'
--   - generalization: ϱ a state → ρ any complex matrix on I × J; reason: the implication uses no property of ρ; it specializes to states
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.2 (unnormalized, 'This however implies, that for some finite N, they are able to obtain an inseparable two-qubit state')

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_BoundEntPPT_IsDistillable
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.2 (unnumbered): "Suppose now that the state ϱ is distillable. This means, that
Alice and Bob are able to obtain pure singlet two-qubit pairs for N tending to infinity. This
however implies, that for some finite N, they are able to obtain an inseparable two-qubit state
ϱ̃_{2q}."

If `ρ` is distillable, then for some finite `N` some operation of type (4)–(5) produces a
two-qubit output that is not separable (not in the cone of Eq. (2)).

**Formalization Note.** Separability is the published cone `Entanglement.IsSeparablePositive`
(Eq. (2) without `Σ p_i = 1`, as p.2 prescribes for unnormalized states). No hypothesis on `ρ`
is needed: the implication holds for every complex matrix (a generalization). Reading of
"distillable": `IsDistillable` (one output pair, Eq. (4) operations, positive success
probability). -/
theorem exists_inseparable_output_of_distillable {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (ρ : Matrix (I × J) (I × J) ℂ) (hD : IsDistillable ρ) :
    ∃ N m : ℕ, ∃ A : Fin m → Matrix (Fin 2) (Fin N → I) ℂ,
      ∃ B : Fin m → Matrix (Fin 2) (Fin N → J) ℂ,
        ¬ QAlgorithms.Entanglement.IsSeparablePositive (localOutput ρ N A B) := by sorry

end BoundEntPPT
