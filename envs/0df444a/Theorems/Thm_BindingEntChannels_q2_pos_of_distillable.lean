-- Prove2me | Theorems.Thm_BindingEntChannels_q2_pos_of_distillable
-- name    : BindingEntChannels.q2_pos_of_distillable
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:54.053928+00:00
-- url     : https://prove2.me/theorems/dc51ccbc-e97f-4606-9c76-717d9d2ec797
-- title:
--   §II, p. 2 — if $(I\otimes\Lambda)P^m_+$ is FE then $Q_2(\Lambda)>0$
-- statement:
--   Let $m\ge1$ and let $\Lambda:M_m\to M_n$ be a channel. If $(I\otimes\Lambda)P^m_+$ is distillable (free entangled), then
--
--   $$
--   Q_2(\Lambda)>0 ,
--   $$
--
--   so condition (i) of the Definition fails.
--
--   Differences from the source:
--   - encoding: P^m_+ of Eq. (1) for a dimension m → hypothesis 0 < m; reason: Eq. (1) divides by √m and is undefined at m = 0
--   - encoding: channel = completely positive trace-preserving map M_m → M_n → IsChannel: a finite Kraus family with Σ E†E = 1; reason: in finite dimension these are the same maps
--   - encoding: Q2(Λ), the two-way assisted capacity of ref. [13] → the platform's twoWayQuantumCapacity with a one-point classical output (flag type Unit, Measure.dirac ()); reason: a channel without classical output; the flag integral is evaluation at the single point
--   - reading: FE (free entanglement) and BE (bound entanglement) → FE = distillable (definition of ref. [3]); BE = density matrix, not separable, not distillable; reason: p. 1: FE "can be converted into pure singlet form", BE "cannot be distilled"; p. 2: a non-BE state "can be separable or FE"
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem: "If its is FE, then one can distill it and obtain nonzero Q2")

import Mathlib
import Definitions.Def_BindingEntChannels_choiState
import Definitions.Def_BindingEntChannels_q2
import Definitions.Def_BoundEntPPT_IsDistillable

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (proof of the Theorem, necessity): "If its is FE, then one can distill it and obtain
nonzero Q₂ so that the condition (i) is violated."

For `0 < m` and a channel `Λ : M_m → M_n`: if `(I ⊗ Λ)P^m_+` is distillable, then `Q₂(Λ) > 0`.

**Formalization Note.** "its" is the paper's typo for "it"; the subject is `(I_m ⊗ Λ^n_m)P^m_+`.
"FE" is `BoundEntPPT.IsDistillable`. -/
theorem q2_pos_of_distillable {m n : ℕ} (hm : 0 < m)
    (Λ : QAlgorithms.Superop (Fin m) (Fin n)) (hΛ : QAlgorithms.IsChannel Λ)
    (h : BoundEntPPT.IsDistillable (choiState Λ)) : 0 < q2 Λ := by sorry

end BindingEntChannels
