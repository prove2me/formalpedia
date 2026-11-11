-- Prove2me | Theorems.Thm_ArbLindbladLearn_lemma_4_2
-- name    : ArbLindbladLearn.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:28:04.016212+00:00
-- url     : https://prove2.me/theorems/0b562bca-f577-42d5-a263-1a6fc8a45eb8
-- title:
--   Lemma 4.2 — coefficient identities (21)–(23)
-- statement:
--   Let $f_A(t)=\langle\Phi_A|J_t|\Phi_A\rangle$. For every nonidentity Pauli label $a$,
--   $$h_a=f'_{A^{\mathrm i}_{a0}}(0)-\tfrac12\big(f'_{P_a}(0)+f'_I(0)\big)\quad(21),\qquad\gamma_{aa}=f'_{P_a}(0)\quad(22),$$
--   and for every pair of distinct nonidentity labels $a,b$,
--   $$\gamma_{ab}=\Big[f'_{A_{ab}}(0)-\tfrac12\big(f'_{P_a}(0)+f'_{P_b}(0)\big)\Big]+\mathrm i\Big[\tfrac12\big(f'_{P_a}(0)+f'_{P_b}(0)\big)-f'_{A^{\mathrm i}_{ab}}(0)\Big]\quad(23).$$
--
--   All coefficients are thus linear combinations of endpoint derivatives of diagonal signals, which the coefficient-learning stage estimates.
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ with P_a = ⊗ᵢ(−i)^{zᵢxᵢ}Z^{zᵢ}X^{xᵢ} → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: a Lindbladian ℒ of the form (8) with h_a ∈ ℝ and γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the generator gen c; reason: ℒ is determined by its coefficients (Lemma 3.1) and every such coefficient vector gives a Lindbladian; same instances
--   - encoding: f_A(t) = ⟨Φ_A|J_t|Φ_A⟩ and its derivative at 0 → the real part of f_A(t) and its two-sided derivative at 0; reason: f_A is real (J_t Hermitian) and entire in t
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 4.2, eqs. (21)–(23), p.26

import Mathlib
import Definitions.Def_ArbLindbladLearn_signal
import Definitions.Def_ArbLindbladLearn_pairWitness
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Lemma 4.2 (Coefficient identities; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), eqs. (21)–(23), p.26). For
every nonidentity Pauli label `a`,
`h_a = f′_{A^i_{a0}}(0) − ½(f′_{P_a}(0) + f′_I(0))` (21) and `γ_aa = f′_{P_a}(0)` (22); for every pair
of distinct nonidentity labels `a, b`,
`γ_ab = [f′_{A_ab}(0) − ½(f′_{P_a}(0) + f′_{P_b}(0))] + i[½(f′_{P_a}(0) + f′_{P_b}(0)) − f′_{A^i_ab}(0)]`
(23).

**Formalization Note** `f_A(t) = ⟨Φ_A|J_t|Φ_A⟩` is the real function `witnessSignal c A`;
`I = pauliMatrix 0`; `A_ab = pairWitness a b`, `A^i_ab = pairWitnessI a b` (Definition 4.1, p.25).
`IsLindbladCoeffs c` says the Kossakowski matrix is Hermitian PSD (Definition 2.6). -/
theorem lemma_4_2 {n : ℕ} (c : Coeffs n) (hc : IsLindbladCoeffs c) :
    (∀ a : Pauli n, a ≠ 0 →
      c.h a = deriv (witnessSignal c (pairWitnessI a 0)) 0 -
        (deriv (witnessSignal c (pauliMatrix a)) 0 +
          deriv (witnessSignal c (pauliMatrix 0)) 0) / 2) ∧
    (∀ a : Pauli n, a ≠ 0 → c.γ a a = ((deriv (witnessSignal c (pauliMatrix a)) 0 : ℝ) : ℂ)) ∧
    (∀ a b : Pauli n, a ≠ 0 → b ≠ 0 → a ≠ b →
      c.γ a b =
        ⟨deriv (witnessSignal c (pairWitness a b)) 0 -
            (deriv (witnessSignal c (pauliMatrix a)) 0 +
              deriv (witnessSignal c (pauliMatrix b)) 0) / 2,
          (deriv (witnessSignal c (pauliMatrix a)) 0 +
              deriv (witnessSignal c (pauliMatrix b)) 0) / 2 -
            deriv (witnessSignal c (pairWitnessI a b)) 0⟩) := by sorry

end ArbLindbladLearn
