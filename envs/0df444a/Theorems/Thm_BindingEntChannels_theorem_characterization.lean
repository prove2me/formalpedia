-- Prove2me | Theorems.Thm_BindingEntChannels_theorem_characterization
-- name    : BindingEntChannels.theorem_characterization
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:13.997409+00:00
-- url     : https://prove2.me/theorems/75dfd56e-6e04-4a6d-8bc0-fa986beb21fd
-- title:
--   Theorem — $\Lambda$ is a binding entanglement channel iff $(I\otimes\Lambda)P^m_+$ is bound entangled
-- statement:
--   Let $m\ge1$ and let $\Lambda:M_m\to M_n$ be a channel (a completely positive trace-preserving map). Then $\Lambda$ is a binding entanglement channel, i.e.
--
--   1. $Q_2(\Lambda)=0$, and
--   2. some bipartite bound entangled state can be obtained by (possibly multiple) uses of $\Lambda$ and LQCC operations,
--
--   if and only if
--
--   $$
--   (I\otimes\Lambda)P^m_+\ \text{is a bound entangled state on}\ \mathbb C^m\otimes\mathbb C^n .
--   $$
--
--   The Theorem reduces a condition on all protocols and on an asymptotic capacity to a property of one state, the state obtained by sending half of a maximally entangled pair through the channel.
--
--   **Formalization Note** $Q_2$ is the operational two-way assisted capacity; protocols are adaptive and may post-select; BE means a density matrix that is neither separable nor distillable. No dimension is fixed and no PPT assumption is made.
--
--   Differences from the source:
--   - encoding: P^m_+ of Eq. (1) for a dimension m → hypothesis 0 < m; reason: Eq. (1) divides by √m and is undefined at m = 0
--   - encoding: channel = completely positive trace-preserving map M_m → M_n → IsChannel: a finite Kraus family with Σ E†E = 1; reason: in finite dimension these are the same maps
--   - reading: LQCC operations → adaptive protocols that may also discard branches (post-selection); reason: the paper calls a non-trace-preserving Γ ⊗ I (p. 2) and filtering (p. 3) LQCC actions; this is the larger class, and the obtained state of M1 needs no post-selection, so nothing is lost for the deterministic class
--   - reading: use of the channel and LQCC operations → protocols in which channel uses and local instruments are interleaved and later steps depend on earlier outcomes; reason: Q2 of ref. [13] is defined with adaptive protocols; non-adaptive protocols are a special case, so this is the more general reading
--   - reading: FE (free entanglement) and BE (bound entanglement) → FE = distillable (definition of ref. [3]); BE = density matrix, not separable, not distillable; reason: p. 1: FE "can be converted into pure singlet form", BE "cannot be distilled"; p. 2: a non-BE state "can be separable or FE"
--   - encoding: Q2(Λ), the two-way assisted capacity of ref. [13] → the platform's twoWayQuantumCapacity with a one-point classical output (flag type Unit, Measure.dirac ()); reason: a channel without classical output; the flag integral is evaluation at the single point
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, Theorem, p. 2

import Mathlib
import Definitions.Def_BindingEntChannels_choiState
import Definitions.Def_BindingEntChannels_IsBindingEntanglementChannel

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, Theorem, p. 2: "A channel Λ : M_m → M_n is binding entanglement iff the state (I ⊗ Λ)P^m_+
(acting on C^m ⊗ C^n) is a BE state."

For `0 < m` and every channel (CPTP map) `Λ : M_m → M_n`: `Λ` is a binding entanglement channel
— `Q₂(Λ) = 0` and some bound entangled state can be obtained from `Λ` by (possibly multiple)
channel uses and LQCC — if and only if `(I ⊗ Λ)P^m_+` is bound entangled.

**Formalization Note.** `Q₂` is the operational two-way assisted capacity (`q2`), protocols are
adaptive and may post-select (`IsObtainable`, reading "LQCC" as including filtering, as the paper
does on pp. 2–3), "BE" is `IsBoundEntangled` (density matrix, not separable, not distillable).
`0 < m` because Eq. (1) is undefined at `m = 0`; `0 < n` follows from `IsChannel Λ`. No
dimension is fixed and no PPT assumption is made. -/
theorem theorem_characterization {m n : ℕ} (hm : 0 < m)
    (Λ : QAlgorithms.Superop (Fin m) (Fin n)) (hΛ : QAlgorithms.IsChannel Λ) :
    IsBindingEntanglementChannel Λ ↔ IsBoundEntangled (choiState Λ) := by sorry

end BindingEntChannels
