-- Prove2me | Theorems.Thm_ArbLindbladLearn_lemma_3_3
-- name    : ArbLindbladLearn.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:28:08.563083+00:00
-- url     : https://prove2.me/theorems/7742f934-1ff8-4bc4-a581-988a0c46c364
-- title:
--   Lemma 3.3 — Bell matrices of the dynamics
-- statement:
--   Let $\mathcal L$ be an $n$-qubit Lindbladian, $J_t=(\mathrm{id}\otimes e^{t\mathcal L})(|\Phi_0\rangle\langle\Phi_0|)$ and $J_0'=(\mathrm{id}\otimes\mathcal L)(|\Phi_0\rangle\langle\Phi_0|)$. For all Pauli labels $a,b$ and all $t\ge0$,
--   $$g_{ab}(t)=\langle\Phi_a|J_t|\Phi_b\rangle=\chi_{ab}(t),\qquad g_{ab}'(0)=\langle\Phi_a|J_0'|\Phi_b\rangle=\chi_{ab},$$
--   where $\chi_{ab}(t)$ and $\chi_{ab}$ are the $\chi$-matrices of $e^{t\mathcal L}$ and $\mathcal L$. Consequently, for all nonidentity labels $a,b$,
--   $$h_a=\mathrm{Im}\langle\Phi_0|J_0'|\Phi_a\rangle=\mathrm{Im}\,g_{0a}'(0),\qquad\gamma_{ab}=\langle\Phi_a|J_0'|\Phi_b\rangle=g_{ab}'(0).$$
--
--   In the Bell basis the endpoint derivative of the Choi state is exactly the $\chi$-matrix of the generator, which is how the coefficients become accessible from time evolution.
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ with P_a = ⊗ᵢ(−i)^{zᵢxᵢ}Z^{zᵢ}X^{xᵢ} → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: a Lindbladian ℒ of the form (8) with h_a ∈ ℝ and γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the generator gen c; reason: ℒ is determined by its coefficients (Lemma 3.1) and every such coefficient vector gives a Lindbladian; same instances
--   - encoding: g′_ab(0), the derivative of g_ab on t ≥ 0 at the endpoint → deriv (two-sided) at 0; reason: g_ab(t) is entire in t (matrix exponential), so both derivatives exist and agree
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 3.3, p.19

import Mathlib
import Definitions.Def_ArbLindbladLearn_signal
import Definitions.Def_ArbLindbladLearn_chiCoeff
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Lemma 3.3 (Bell matrices of the dynamics; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.19). For all Pauli
labels `a, b` and all `t ≥ 0`, `g_ab(t) = ⟨Φ_a|J_t|Φ_b⟩ = χ_ab(t)` and
`g′_ab(0) = ⟨Φ_a|J′₀|Φ_b⟩ = χ_ab`. Consequently, for all nonidentity labels `a, b`,
`h_a = Im⟨Φ₀|J′₀|Φ_a⟩ = Im g′_0a(0)` and `γ_ab = ⟨Φ_a|J′₀|Φ_b⟩ = g′_ab(0)`.

**Formalization Note** `J_t = choiJ (e^{tℒ})` and `J′₀ = choiJ ℒ = (id ⊗ ℒ)(|Φ₀⟩⟨Φ₀|)` (p.19);
`χ_ab(t)` and `χ_ab` are the `χ`-matrices of `e^{tℒ}` and `ℒ` (eq. (13), `chiCoeff`). `g_ab` is
entire in `t`, so its two-sided derivative at `0` (`deriv`) equals the one-sided one. -/
theorem lemma_3_3 {n : ℕ} (c : Coeffs n) (hc : IsLindbladCoeffs c) :
    (∀ a b : Pauli n, ∀ t : ℝ, 0 ≤ t →
      bellCoh c a b t = chiCoeff (evolution (gen c) t) a b) ∧
    (∀ a b : Pauli n,
      deriv (fun t => bellCoh c a b t) 0 =
          bellForm (choiJ (gen c)) (bellVec (pauliMatrix a)) (bellVec (pauliMatrix b)) ∧
        bellForm (choiJ (gen c)) (bellVec (pauliMatrix a)) (bellVec (pauliMatrix b)) =
          chiCoeff (gen c) a b) ∧
    (∀ a : Pauli n, a ≠ 0 →
      c.h a =
          (bellForm (choiJ (gen c)) (bellVec (pauliMatrix 0)) (bellVec (pauliMatrix a))).im ∧
        (bellForm (choiJ (gen c)) (bellVec (pauliMatrix 0)) (bellVec (pauliMatrix a))).im =
          (deriv (fun t => bellCoh c 0 a t) 0).im) ∧
    (∀ a b : Pauli n, a ≠ 0 → b ≠ 0 →
      c.γ a b = bellForm (choiJ (gen c)) (bellVec (pauliMatrix a)) (bellVec (pauliMatrix b)) ∧
        bellForm (choiJ (gen c)) (bellVec (pauliMatrix a)) (bellVec (pauliMatrix b)) =
          deriv (fun t => bellCoh c a b t) 0) := by sorry

end ArbLindbladLearn
