-- Prove2me | Theorems.Thm_BindingEntChannels_eq_2
-- name    : BindingEntChannels.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:40:04.585576+00:00
-- url     : https://prove2.me/theorems/dcabcdfc-db34-4b18-809f-6aacc6df5071
-- title:
--   Eq. (2) — $(I\otimes\Lambda)(\Gamma\otimes I)P_+=(\Gamma\otimes\Lambda)P_+=(\Gamma\otimes I)(I\otimes\Lambda)P_+$
-- statement:
--   Let $\Lambda(X)=\sum_l E_lXE_l^\dagger$ be a completely positive map from operators on $\mathbb C^I$ to operators on $\mathbb C^O$ and $\Gamma(X)=\sum_j G_jXG_j^\dagger$ one from $\mathbb C^I$ to $\mathbb C^K$, both given by finite Kraus families. Then
--
--   $$
--   (I\otimes\Lambda)(\Gamma\otimes I)P^I_+=\sum_{j,l}(G_j\otimes E_l)\,P^I_+\,(G_j\otimes E_l)^\dagger=(\Gamma\otimes I)(I\otimes\Lambda)P^I_+ .
--   $$
--
--   The middle term is $(\Gamma\otimes\Lambda)P^I_+$. The identity moves Alice's preparation map past the channel, so the output of the two-stage protocol is a local filter applied to $(I\otimes\Lambda)P_+$.
--
--   Differences from the source:
--   - generalization: Λ^{⊗N} a channel and Γ CP, on C^{m×N} → any CP map Λ given by a Kraus family E and any CP Γ, on arbitrary finite index sets; reason: the paper's case is I = Fin N → Fin m with Λ^{⊗N}, which has a Kraus form
--   - encoding: (Γ ⊗ Λ)P_+ → Σ_{j,l} (G_j ⊗ E_l) P_+ (G_j ⊗ E_l)†; reason: the Kraus form of the tensor product of two CP maps
--   - encoding: Γ is CP, but not necessarily trace-preserving → Γ given by a finite Kraus family G with no completeness condition; reason: every CP map between finite-dimensional matrix algebras has a finite Kraus form
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, Eq. (2), p. 2

import Mathlib
import Definitions.Def_BindingEntChannels_choiState
import Definitions.Def_BindingEntChannels_filterLeft

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, Eq. (2), p. 2:
`ϱ = (I ⊗ Λ)(Γ ⊗ I)P_+ = (Γ ⊗ Λ)P_+ = (Γ ⊗ I)(I ⊗ Λ)P_+`.

For a CP map `Λ : M_I → M_O` with Kraus family `E` and a CP map `Γ : M_I → M_K` with Kraus
family `G`: applying `Λ` to the second half of `(Γ ⊗ I)P^I_+` gives
`Σ_{j,l} (G_j ⊗ E_l) P^I_+ (G_j ⊗ E_l)†`, which equals `(Γ ⊗ I)` applied to `(I ⊗ Λ)P^I_+`.

**Formalization Note.** The paper's Eq. (2) is for `Λ^{⊗N}` on `N` copies; this is the general
form for any finite index types (the paper's case is `I = Fin N → Fin m`). `Λ` need only be
given by a Kraus family `E` (no completeness condition), and `Γ ⊗ Λ` is written with the
product Kraus operators `G_j ⊗ E_l`. `P^I_+` is the published `ObliviousRSP.maxEnt I`. -/
theorem eq_2 {I : Type} {O K : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O] {r s : ℕ}
    (G : Fin r → Matrix K I ℂ) (E : Fin s → Matrix O I ℂ) (Λ : QAlgorithms.Superop I O)
    (hE : ∀ X, Λ X = QAlgorithms.krausApply E X) :
    QAlgorithms.idTensorSuperop (R := K) Λ (filterLeft G (ObliviousRSP.maxEnt I)) =
        ∑ j, ∑ l, Matrix.kronecker (G j) (E l) * ObliviousRSP.maxEnt I * (Matrix.kronecker (G j) (E l))ᴴ ∧
      ∑ j, ∑ l, Matrix.kronecker (G j) (E l) * ObliviousRSP.maxEnt I * (Matrix.kronecker (G j) (E l))ᴴ =
        filterLeft G (choiState Λ) := by sorry

end BindingEntChannels
