-- Prove2me | Theorems.Thm_DHRUniq_lemma_15
-- name    : DHRUniq.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:01.657679+00:00
-- url     : https://prove2.me/theorems/0a63e902-7161-4317-8e9f-c17deeda6276
-- title:
--   Lemma 15: every state is reachable from $P_+^d$ and maps to a product state
-- statement:
--   Let $\mathcal H^A\equiv\mathcal H^B\equiv\mathcal H$ with $\dim\mathcal H=d$, let $\varrho$ be a state on $\mathcal H^A\otimes\mathcal H^B$, let $|\phi\rangle=|\phi^A\rangle\otimes|\phi^B\rangle$ be a separable wavefunction, and let $P_+^d$ be a representative of $P_+(\mathbb C^d)$ on $\mathcal H^A\otimes\mathcal H^B$. Then there exist LQCC operations $\Lambda_1$ and $\Lambda_2$ with
--
--   $$
--   \Lambda_1(\varrho)=|\phi\rangle\langle\phi|,\qquad\Lambda_2(P_+^d)=\varrho.
--   $$
--
--   Together with (P2) this bounds a measure on all pure states of a fixed space between the values on a product state and on a maximally entangled state.
--
--   Differences from the source:
--   - encoding: H^A ≡ H^B ≡ H, dim H = d → one finite type H used for both factors, with Fintype.card H = d; reason: this is the paper's identification, with the standard basis of ℂ^H
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Lemma 15, p. 13

import Mathlib
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_DHRUniq_IsMaxEntRep
import Definitions.Def_DHRUniq_IsLQCC
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)
open WildeQIT (IsDensityOperator)

namespace DHRUniq

/-- **Lemma 15** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, Lemma 15, p. 13): "Let `ϱ ∈ Σ(H^A ⊗ H^B)` with `H^A ≡ H^B ≡ H` and
`dim H = d`. Let `|φ⟩ = |φ^A⟩ ⊗ |φ^B⟩ ∈ H^A ⊗ H^B` be a separable wavefunction and `P_+^d` be a
representative of `P_+(ℂ^d)` on `H^A ⊗ H^B`. Then there exist LQCC operations `Λ_1` and `Λ_2` such that
`Λ_1(ϱ) = |φ⟩⟨φ|` and `Λ_2(P_+^d) = ϱ`."

**Formalization Note** One finite type `H` serves as both local spaces. `ϱ` is any density operator,
mixed or pure. -/
theorem lemma_15 {H : Type} [Fintype H] [DecidableEq H] (d : ℕ) (hd : Fintype.card H = d)
    (ρ : Matrix (H × H) (H × H) ℂ) (hρ : IsDensityOperator ρ) (φA φB : H → ℂ)
    (hφA : IsUnitVec φA) (hφB : IsUnitVec φB) (P : H × H → ℂ) (hP : IsMaxEntRep d P) :
    ∃ Λ₁ Λ₂ : Matrix (H × H) (H × H) ℂ → Matrix (H × H) (H × H) ℂ,
      IsLQCC Λ₁ ∧ IsLQCC Λ₂ ∧ Λ₁ ρ = pureState (fun z => φA z.1 * φB z.2) ∧
        Λ₂ (pureState P) = ρ := by sorry

end DHRUniq
