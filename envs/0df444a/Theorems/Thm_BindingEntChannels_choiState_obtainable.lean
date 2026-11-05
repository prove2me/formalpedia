-- Prove2me | Theorems.Thm_BindingEntChannels_choiState_obtainable
-- name    : BindingEntChannels.choiState_obtainable
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:40:56.178798+00:00
-- url     : https://prove2.me/theorems/877d9172-5a04-4d54-b934-90260a8817a8
-- title:
--   §II, p. 2 — $(I\otimes\Lambda)P^m_+$ is obtained by one use of the channel, so (ii) holds if it is BE
-- statement:
--   Let $m\ge1$ and let $\Lambda:M_m\to M_n$ be a channel. Then:
--
--   1. the state $(I\otimes\Lambda)P^m_+$ is obtainable from $\Lambda$ by a protocol, so clause (ii) of the Definition holds whenever this state is bound entangled;
--   2. explicitly, if Alice holds the singlet $P^m_+$ in her memory $\mathbb C^m\otimes\mathbb C^m$ and Bob's memory is one-dimensional, sending the second half of the singlet through $\Lambda$ once yields exactly
--
--   $$
--   (I\otimes\Lambda)P^m_+ .
--   $$
--
--   This is the sufficiency half of clause (ii): the state needs one channel use, no measurement, no post-selection and no classical communication.
--
--   **Formalization Note** Alice's memory $\mathbb C^{m\cdot m}$ is identified with $\mathbb C^m\otimes\mathbb C^m$ by the standard bijection $\mathrm{Fin}(m\cdot m)\simeq\mathrm{Fin}\,m\times\mathrm{Fin}\,m$; the relabelling of Bob's memory is existential.
--
--   Differences from the source:
--   - encoding: P^m_+ of Eq. (1) for a dimension m → hypothesis 0 < m; reason: Eq. (1) divides by √m and is undefined at m = 0
--   - encoding: channel = completely positive trace-preserving map M_m → M_n → IsChannel: a finite Kraus family with Σ E†E = 1; reason: in finite dimension these are the same maps
--   - reading: LQCC operations → adaptive protocols that may also discard branches (post-selection); reason: the paper calls a non-trace-preserving Γ ⊗ I (p. 2) and filtering (p. 3) LQCC actions; this is the larger class, and the obtained state of M1 needs no post-selection, so nothing is lost for the deterministic class
--   - reading: use of the channel and LQCC operations → protocols in which channel uses and local instruments are interleaved and later steps depend on earlier outcomes; reason: Q2 of ref. [13] is defined with adaptive protocols; non-adaptive protocols are a special case, so this is the more general reading
--   - generalization: if (I ⊗ Λ)P^m_+ is BE then (ii) is obviously satisfied → (I ⊗ Λ)P^m_+ is obtainable for every channel (no BE hypothesis), and explicitly one sendVia of the second half of the singlet held by Alice yields it; reason: the second conjunct is the closing remark of §II, p. 2 ("merely by sending half of singlet pair through the channel"); at a BE state the first conjunct gives the sentence
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem: "If (I ⊗ Λ^n_m)P^m_+ is BE state then (ii) is obviously satisfied"; and the closing remark of §II)

import Mathlib
import Definitions.Def_BindingEntChannels_choiState
import Definitions.Def_BindingEntChannels_IsObtainable

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (proof of the Theorem, sufficiency, and the closing remark of §II): "If
`(I ⊗ Λ^n_m)P^m_+` is BE state then (ii) is obviously satisfied"; "it can be created without
exchange of classical information between Alice and Bob but merely by sending half of singlet
pair through the channel."

For `0 < m` and a channel `Λ : M_m → M_n`: (1) `(I ⊗ Λ)P^m_+` is obtainable by a protocol
(clause (ii) of the Definition), and (2) explicitly, if Alice holds the singlet `P^m_+` in her
memory `Fin (m*m) ≅ Fin m × Fin m` and Bob's memory is one-dimensional, one channel use on the
second half of the singlet yields exactly `(I ⊗ Λ)P^m_+`.

**Formalization Note.** Clause (2) displays the witness: no measurement, no post-selection, no
classical communication. Alice's memory `Fin (m*m)` is identified with `Fin m × Fin m` by
`finProdFinEquiv`; the relabelling `f` of Bob's memory is existential (any `Fin n ≃ Fin n × Fin 1`
works). The singlet `P^m_+` is the published `ObliviousRSP.maxEnt (Fin m)`. -/
theorem choiState_obtainable {m n : ℕ} (hm : 0 < m) (Λ : QAlgorithms.Superop (Fin m) (Fin n))
    (hΛ : QAlgorithms.IsChannel Λ) :
    IsObtainable Λ (choiState Λ) ∧
      ∃ f : Fin n ≃ Fin n × Fin 1,
        RetroCorr.Separation.sendVia finProdFinEquiv.symm f Λ
          (Matrix.of fun p q : Fin (m * m) × Fin 1 =>
            ObliviousRSP.maxEnt (Fin m) (finProdFinEquiv.symm p.1) (finProdFinEquiv.symm q.1)) =
          choiState Λ := by sorry

end BindingEntChannels
