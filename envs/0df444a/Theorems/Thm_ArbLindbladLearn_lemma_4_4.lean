-- Prove2me | Theorems.Thm_ArbLindbladLearn_lemma_4_4
-- name    : ArbLindbladLearn.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:29:31.139764+00:00
-- url     : https://prove2.me/theorems/345b5bdb-d753-4516-80aa-2beb33dec9b2
-- title:
--   Lemma 4.4 — two-sided process shadow $\mathbb E[\hat J_t]=J_t$
-- statement:
--   Fix $t\ge0$. Sample $\psi$ uniformly from $\mathrm{Stab}_n$, evolve under $e^{t\mathcal L}$, apply an independent uniformly random Clifford $C$, measure in the computational basis to obtain $b$, and set $\phi=C^\dagger|b\rangle\langle b|C$. The snapshot $\hat J_t=((d+1)\psi^\top-I)\otimes((d+1)\phi-I)$ satisfies
--   $$\mathbb E[\hat J_t]=J_t .$$
--
--   The Choi state is never prepared; its unbiased classical estimate comes from ancilla-free experiments.
--
--   Differences from the source:
--   - encoding: a Lindbladian ℒ of the form (8) with h_a ∈ ℝ and γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the generator gen c; reason: ℒ is determined by its coefficients (Lemma 3.1) and every such coefficient vector gives a Lindbladian; same instances
--   - reading: φ = C†|b⟩⟨b|C for a uniformly random Clifford C and Born outcome b → the outcome law of eq. (29): given ψ, φ ∈ Stab_n with probability d·tr(e^{tℒ}(ψ)φ)/|Stab_n|; reason: a uniform measure on Cl_n is defined only up to global phases; (29) is the law the paper derives from it and uses in the proof
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 4.4, p.28 (eqs. (28)–(29))

import Mathlib
import Definitions.Def_ArbLindbladLearn_snapshot
import Definitions.Def_ArbLindbladLearn_signal
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Lemma 4.4 (Two-sided process shadow; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.28). For the
random-Clifford-probing experiment at time `t ≥ 0` (sample a uniformly random `ψ ∈ Stab_n`, evolve
under `e^{tℒ}`, apply an independent uniformly random Clifford `C`, measure `b`, set `φ = C†|b⟩⟨b|C`),
the snapshot `Ĵ_t = ((d+1)ψ^⊤ − I) ⊗ ((d+1)φ − I)` (eq. (28)) satisfies `E[Ĵ_t] = J_t`.

**Formalization Note** The recorded pair `(ψ, φ)` has the law `shadowWeight`: `ψ` uniform on `Stab_n`, then `φ ∈ Stab_n`
with probability `d·tr(e^{tℒ}(ψ)φ)/|Stab_n|` (eq. (29), p.28), the law of `φ = C†|b⟩⟨b|C` for a
uniformly random Clifford `C` and the computational-basis outcome `b`. Both `Ĵ_t` and `J_t = choiJ (e^{tℒ})` have the reference factor first.
`IsLindbladCoeffs c` makes `e^{tℒ}` a channel for `t ≥ 0`. -/
theorem lemma_4_4 {n : ℕ} (c : Coeffs n) (hc : IsLindbladCoeffs c) (t : ℝ) (ht : 0 ≤ t) :
    shadowExpect c t (fun ψ φ => snapshot ψ φ) = choiJ (evolution (gen c) t) := by sorry

end ArbLindbladLearn
