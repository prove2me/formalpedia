-- Prove2me | Theorems.Thm_BindingEntChannels_isSeparable_of_obtainable
-- name    : BindingEntChannels.isSeparable_of_obtainable
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:04.928249+00:00
-- url     : https://prove2.me/theorems/c468f2be-8f1b-4a0e-aeb2-06fc94df4478
-- title:
--   §II, p. 2 — if $(I\otimes\Lambda)P^m_+$ is separable, condition (ii) fails
-- statement:
--   Let $m\ge1$ and let $\Lambda:M_m\to M_n$ be a channel such that $(I\otimes\Lambda)P^m_+$ is separable. Then every bipartite state obtainable from $\Lambda$, by any number of channel uses and any adaptive LQCC protocol with post-selection, is separable.
--
--   In particular no bound entangled state is obtainable, so condition (ii) of the Definition fails.
--
--   Differences from the source:
--   - encoding: (Λ^n_m ⊗ I_m)P^m_+ is separable (as printed) → (I_m ⊗ Λ)P^m_+ is separable; reason: P^m_+ is symmetric, so the two states are exchanged by swapping the tensor factors, which preserves separability; the rest of the proof and the Theorem use (I_m ⊗ Λ)P^m_+
--   - generalization: condition (ii) is violated (no BE state is obtainable) → every obtainable state is separable; reason: separable states are not BE
--   - encoding: P^m_+ of Eq. (1) for a dimension m → hypothesis 0 < m; reason: Eq. (1) divides by √m and is undefined at m = 0
--   - encoding: channel = completely positive trace-preserving map M_m → M_n → IsChannel: a finite Kraus family with Σ E†E = 1; reason: in finite dimension these are the same maps
--   - reading: LQCC operations → adaptive protocols that may also discard branches (post-selection); reason: the paper calls a non-trace-preserving Γ ⊗ I (p. 2) and filtering (p. 3) LQCC actions; this is the larger class, and the obtained state of M1 needs no post-selection, so nothing is lost for the deterministic class
--   - reading: use of the channel and LQCC operations → protocols in which channel uses and local instruments are interleaved and later steps depend on earlier outcomes; reason: Q2 of ref. [13] is defined with adaptive protocols; non-adaptive protocols are a special case, so this is the more general reading
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem: "If, instead (Λ^n_m ⊗ I_m)P^m_+ is separable, then we will show that the condition (ii) is violated.")

import Mathlib
import Definitions.Def_BindingEntChannels_choiState
import Definitions.Def_BindingEntChannels_IsObtainable
import Definitions.Def_HorodeckiBoundKey_IsSeparable

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (proof of the Theorem, necessity): "If, instead (Λ^n_m ⊗ I_m)P^m_+ is separable, then
we will show that the condition (ii) is violated."

For `0 < m` and a channel `Λ : M_m → M_n` with `(I ⊗ Λ)P^m_+` separable, every state obtainable
from `Λ` by any protocol (any number of channel uses, adaptive LQCC, post-selection) is
separable; in particular no BE state is obtainable.

**Formalization Note.** The paper prints `(Λ^n_m ⊗ I_m)P^m_+` here, a typo for
`(I_m ⊗ Λ^n_m)P^m_+` (the next sentence and the Theorem use the latter); the statement uses
`choiState Λ`, the latter. -/
theorem isSeparable_of_obtainable {m n : ℕ} (hm : 0 < m)
    (Λ : QAlgorithms.Superop (Fin m) (Fin n)) (hΛ : QAlgorithms.IsChannel Λ)
    (hsep : HorodeckiBoundKey.IsSeparable (choiState Λ)) {c d : ℕ}
    (ρ : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) (hρ : IsObtainable Λ ρ) :
    HorodeckiBoundKey.IsSeparable ρ := by sorry

end BindingEntChannels
