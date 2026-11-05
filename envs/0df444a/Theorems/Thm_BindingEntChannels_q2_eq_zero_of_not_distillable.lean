-- Prove2me | Theorems.Thm_BindingEntChannels_q2_eq_zero_of_not_distillable
-- name    : BindingEntChannels.q2_eq_zero_of_not_distillable
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:40:14.162812+00:00
-- url     : https://prove2.me/theorems/d0f4ed26-469f-4ba8-9be9-15ca217dd3a1
-- title:
--   §II, p. 2 — if $(I\otimes\Lambda)P^m_+$ is BE then $Q_2(\Lambda)=0$ (condition (i))
-- statement:
--   Let $m\ge1$ and let $\Lambda:M_m\to M_n$ be a channel. If $(I\otimes\Lambda)P^m_+$ is not distillable, then
--
--   $$
--   Q_2(\Lambda)=0 .
--   $$
--
--   In particular, if $(I\otimes\Lambda)P^m_+$ is bound entangled, condition (i) of the Definition holds. This completes the sufficiency half of the Theorem.
--
--   Differences from the source:
--   - generalization: (I_m ⊗ Λ)P^m_+ is BE → (I_m ⊗ Λ)P^m_+ is not distillable; reason: BE states are not distillable; entanglement is not used for condition (i)
--   - encoding: P^m_+ of Eq. (1) for a dimension m → hypothesis 0 < m; reason: Eq. (1) divides by √m and is undefined at m = 0
--   - encoding: channel = completely positive trace-preserving map M_m → M_n → IsChannel: a finite Kraus family with Σ E†E = 1; reason: in finite dimension these are the same maps
--   - encoding: Q2(Λ), the two-way assisted capacity of ref. [13] → the platform's twoWayQuantumCapacity with a one-point classical output (flag type Unit, Measure.dirac ()); reason: a channel without classical output; the flag integral is evaluation at the single point
--   - reading: FE (free entanglement) and BE (bound entanglement) → FE = distillable (definition of ref. [3]); BE = density matrix, not separable, not distillable; reason: p. 1: FE "can be converted into pure singlet form", BE "cannot be distilled"; p. 2: a non-BE state "can be separable or FE"
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem: "Hence, if (I_m ⊗ Λ^n_m)P^m_+ is BE then the condition (i) is satisfied.")

import Mathlib
import Definitions.Def_BindingEntChannels_choiState
import Definitions.Def_BindingEntChannels_q2
import Definitions.Def_BoundEntPPT_IsDistillable

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (proof of the Theorem, sufficiency): "Hence, if (I_m ⊗ Λ^n_m)P^m_+ is BE then the
condition (i) is satisfied."

For `0 < m` and a channel `Λ : M_m → M_n`: if `(I ⊗ Λ)P^m_+` is not distillable, then
`Q₂(Λ) = 0`.

**Formalization Note.** Only non-distillability of `(I ⊗ Λ)P^m_+` is assumed, not that it is
entangled; BE states are in particular not distillable. -/
theorem q2_eq_zero_of_not_distillable {m n : ℕ} (hm : 0 < m)
    (Λ : QAlgorithms.Superop (Fin m) (Fin n)) (hΛ : QAlgorithms.IsChannel Λ)
    (h : ¬ BoundEntPPT.IsDistillable (choiState Λ)) : q2 Λ = 0 := by sorry

end BindingEntChannels
