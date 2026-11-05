-- Prove2me | Theorems.Thm_BindingEntChannels_choiState_piSuperop
-- name    : BindingEntChannels.choiState_piSuperop
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:52.792481+00:00
-- url     : https://prove2.me/theorems/58112986-230b-4ada-918e-bf0fd3a78244
-- title:
--   §II, p. 2 — $(I\otimes\Lambda^{\otimes N})P_+=\big((I\otimes\Lambda)P^m_+\big)^{\otimes N}$
-- statement:
--   Let $\Lambda:M_m\to M_n$ be a channel and $N\in\mathbb N$. Sending the second half of the singlet on $(\mathbb C^m)^{\otimes N}\otimes(\mathbb C^m)^{\otimes N}$ through $\Lambda^{\otimes N}$ gives $N$ copies of $(I\otimes\Lambda)P^m_+$:
--
--   $$
--   (I\otimes\Lambda^{\otimes N})P^{m^N}_+=\big((I\otimes\Lambda)P^m_+\big)^{\otimes N},
--   $$
--
--   with Alice's $N$ factors grouped first on both sides.
--
--   **Formalization Note** $\Lambda^{\otimes N}$ is the platform's tensor product of a family of superoperators, here the constant family; the $N$-fold copy is the platform's grouped tensor power, so the two sides live on the same index set with no reordering.
--
--   Differences from the source:
--   - generalization: N ≥ 1 copies → every N ∈ ℕ; reason: at N = 0 both sides are the 1 × 1 matrix 1; for N ≥ 1 it is the paper's identity
--   - encoding: channel = completely positive trace-preserving map M_m → M_n → IsChannel: a finite Kraus family with Σ E†E = 1; reason: in finite dimension these are the same maps
--   - generalization: m ≥ 1 (P^m_+ of Eq. (1)) → every m ∈ ℕ, no hypothesis 0 < m; reason: at m = 0 and N ≥ 1 both sides are empty matrices, at m = 0 and N = 0 both are the 1 × 1 matrix 1; for m ≥ 1 it is the paper's identity
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem)

import Mathlib
import Definitions.Def_BindingEntChannels_choiState
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (proof of the Theorem): "(I_{m×N} ⊗ Λ^{n×N}_{m×N})P^{m×N}_+ = ((I_m ⊗ Λ^n_m)P^m_+)^{⊗N}".

For a channel `Λ : M_m → M_n` and every `N`, sending the second half of the singlet on
`(C^m)^{⊗N}` through `Λ^{⊗N}` gives `N` copies of `(I ⊗ Λ)P^m_+`.

**Formalization Note.** `Λ^{⊗N}` is `QAlgorithms.piSuperop` of the constant family; the
`N`-fold copy is the published `Information100.P04.copies`, which groups Alice's `N` factors
first, so both sides live on `(Fin N → Fin m) × (Fin N → Fin n)` with no reindexing. -/
theorem choiState_piSuperop {m n : ℕ} (N : ℕ) (Λ : QAlgorithms.Superop (Fin m) (Fin n))
    (hΛ : QAlgorithms.IsChannel Λ) :
    choiState (QAlgorithms.piSuperop fun _ : Fin N => Λ) =
      QAlgorithms.Papers.Independent.Information100.P04.copies (choiState Λ) N := by sorry

end BindingEntChannels
