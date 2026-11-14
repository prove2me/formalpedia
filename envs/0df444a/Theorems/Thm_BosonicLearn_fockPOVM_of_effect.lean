-- Prove2me | Theorems.Thm_BosonicLearn_fockPOVM_of_effect
-- name    : BosonicLearn.fockPOVM_of_effect
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T06:12:06.864149+00:00
-- url     : https://prove2.me/theorems/7d8efe0e-fc5e-4395-9519-130c5e961fb8
-- title:
--   A weakly $\sigma$-additive family of effects is a POVM: $B\mapsto\mathrm{Tr}(E(B)\rho)$ is a probability measure
-- statement:
--   A family of effects that is countably additive entry by entry defines a POVM: its Born probabilities are countably additive on every density operator.
--
--   Let $I$ be an index set, $\Omega$ a measurable space, and for every $B\subseteq\Omega$ let $E(B)=(E(B)_{ij})_{i,j\in I}$ be a coefficient array such that
--
--   1. for every measurable $B$ and every finitely supported vector $z$, $\langle z,E(B)z\rangle$ is real with $0\le\langle z,E(B)z\rangle\le\langle z,z\rangle$;
--   2. $E(\Omega)=\mathbf 1$;
--   3. for all $i,j\in I$ and all pairwise disjoint measurable $B_0,B_1,\dots\subseteq\Omega$, $\;E\big(\bigcup_nB_n\big)_{ij}=\sum_nE(B_n)_{ij}$.
--
--   Then there is a POVM on $\ell^2(I)$ with outcomes in $\Omega$ whose effects are $E$. Equivalently, for every density operator $\rho$ on $\ell^2(I)$ the set function
--
--   $$
--   B\longmapsto\operatorname{Re}\operatorname{Tr}(E(B)\rho)=\operatorname{Re}\sum_i\sum_jE(B)_{ij}\rho_{ji}
--   $$
--
--   is a probability measure on $\Omega$.
--
--   Role. A `FockPOVM` carries its outcome law on every density operator as data. This lemma constructs that data from the effects alone, so a POVM on an infinite-dimensional system can be defined by giving matrix entries that are finite combinations of measures. It is the last step in the construction of the sequential composition of two POVMs (`BosonicLearn.fockPOVM_compose`), where the effects on the two-system space are $E'(C)=\int M(\mathrm dx)\otimes Q_x(C_x)$.
--
--   **Formalization Note** The conclusion is `∃ P : FockPOVM I Ω, P.effect = E`; the Born law is then given by the fields `law_prob` and `law_born` of `P`. Hypothesis 3 is `HasSum` of the entries along sequences indexed by $\mathbb N$. Values of $E$ on non-measurable sets are unconstrained.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) and `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators). The proof imports `BosonicLearn.born_truncation` and `BosonicLearn.measure_of_uniform_limit`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5 (general POVM measurements with continuous outcomes); auxiliary lemma for the proof of Theorem 3, p. 67

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **A weakly σ-additive family of effects is a POVM.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5: "All of our theorems stated in Sec. 1.2 hold for general POVM measurements on n-mode
bosonic systems, which are allowed to be non-Gaussian".

Let `E(B)`, for `B ⊆ Ω`, be coefficient arrays on an index set `I` such that
1. for measurable `B`, `0 ≤ ⟨z, E(B) z⟩ ≤ ⟨z, z⟩` (real) for every finitely supported `z`;
2. `E(Ω) = I`;
3. every matrix entry is countably additive: `E(⋃ₙ Bₙ)_ij = ∑ₙ E(Bₙ)_ij` for pairwise disjoint measurable `Bₙ`.

Then there is a POVM on `ℓ²(I)` with outcomes in `Ω` whose effects are exactly `E`. In particular for every
density operator `ρ`, `B ↦ Re Tr(E(B) ρ)` is a probability measure on `Ω`.

**Formalization Note.** The POVM is a `FockPOVM I Ω` with `effect = E`; its fields `law_prob` and `law_born`
give the Born law on every density operator, entangled or not when `I` is a product. -/
theorem fockPOVM_of_effect {I Ω : Type} [DecidableEq I] [MeasurableSpace Ω] (E : Set Ω → Matrix I I ℂ)
    (hform : ∀ B : Set Ω, MeasurableSet B → ∀ (s : Finset I) (z : I → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E B i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E B i j * z j).re ∧
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E B i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2)
    (huniv : E Set.univ = 1)
    (hadd : ∀ (i j : I) (f : ℕ → Set Ω), (∀ n, MeasurableSet (f n)) →
      Pairwise (Function.onFun Disjoint f) → HasSum (fun n => E (f n) i j) (E (⋃ n, f n) i j)) :
    ∃ P : FockPOVM I Ω, P.effect = E := by sorry

end BosonicLearn
