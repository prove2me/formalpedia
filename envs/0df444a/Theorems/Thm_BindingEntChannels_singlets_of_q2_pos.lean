-- Prove2me | Theorems.Thm_BindingEntChannels_singlets_of_q2_pos
-- name    : BindingEntChannels.singlets_of_q2_pos
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:55.016398+00:00
-- url     : https://prove2.me/theorems/d6bee9b7-1e55-49d8-af0b-6156647fa746
-- title:
--   §II, p. 2 — $Q_2(\Lambda)>0$ gives asymptotically pure singlets by the channel and LQCC
-- statement:
--   Let $\Lambda$ be a channel with $Q_2(\Lambda)>0$. Then for every $\varepsilon>0$ there is a protocol, using $\Lambda$ some number $N$ of times together with adaptive LQCC and started from no shared state, whose output is a two-qubit state $\omega$ produced with probability one and with singlet fidelity at least $1-\varepsilon$:
--
--   $$
--   \operatorname{Tr}\omega=1,\qquad \langle\Psi^-|\,\omega\,|\Psi^-\rangle\ \ge\ 1-\varepsilon ,
--   $$
--
--   where $|\Psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$.
--
--   This is the step of the proof that turns a positive capacity into singlets, which are then traced back to free entanglement of $(I\otimes\Lambda)P^m_+$.
--
--   Differences from the source:
--   - reading: one can produce asymptotically pure singlets → for every ε > 0, a two-qubit output with singlet fidelity ≥ 1 − ε; reason: "asymptotically pure" is fidelity tending to one, as in the definition of FE (ref. [3]); the proof uses only that singlets of arbitrarily high fidelity are produced
--   - reading: produce … by use of the channel and LQCC → produced with success probability one (Tr ω = 1, no branch discarded); reason: of the two readings (with or without post-selection) this is the stronger one; it implies the post-selected version
--   - encoding: singlet → the two-qubit Ψ⁻ (the platform's singletState on Fin 2 × Fin 2); reason: the target of the definition of distillability, ref. [3]; it differs from P^2_+ by a local unitary
--   - encoding: channel = completely positive trace-preserving map M_m → M_n → IsChannel: a finite Kraus family with Σ E†E = 1; reason: in finite dimension these are the same maps
--   - reading: use of the channel and LQCC operations → protocols in which channel uses and local instruments are interleaved and later steps depend on earlier outcomes; reason: Q2 of ref. [13] is defined with adaptive protocols; non-adaptive protocols are a special case, so this is the more general reading
--   - encoding: Q2(Λ), the two-way assisted capacity of ref. [13] → the platform's twoWayQuantumCapacity with a one-point classical output (flag type Unit, Measure.dirac ()); reason: a channel without classical output; the flag integral is evaluation at the single point
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem)

import Mathlib
import Definitions.Def_BindingEntChannels_q2
import Definitions.Def_BindingEntChannels_AdaptiveState
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (proof of the Theorem): "Suppose, conversely, that Q₂(Λ^n_m) > 0. Then, one can produce
asymptotically pure singlets by use of the channel and LQCC."

For a channel `Λ` with `Q₂(Λ) > 0` and every `ε > 0` there is a protocol, using the channel
some number `N` of times and started from no shared state, that outputs (with probability one) a
two-qubit state `ω` on `Fin 2 × Fin 2` whose singlet fidelity is at least `1 − ε`:
`Tr ω = 1` and `1 − ε ≤ Re Tr(|Ψ⁻⟩⟨Ψ⁻| ω)`.

**Formalization Note.** The protocol class is `AdaptiveState` (adaptive LQCC, post-selection
allowed); the conclusion `Tr ω = 1` excludes post-selection (no branch is lost), which is the
stronger reading of "produce". "Singlet" here is the two-qubit `Ψ⁻`
(`Dependency50.P42.singletState`), as in the definition of distillability (ref. [3]). -/
theorem singlets_of_q2_pos {m n : ℕ} (Λ : QAlgorithms.Superop (Fin m) (Fin n))
    (hΛ : QAlgorithms.IsChannel Λ) (hq : 0 < q2 Λ) :
    ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (run : QAlgorithms.Superop (Fin 1 × Fin 1) (Fin 2 × Fin 2)),
      AdaptiveState Λ 2 2 (n := N) run ∧ (run 1).trace = 1 ∧
        1 - ε ≤ (QAlgorithms.Papers.Independent.Dependency50.P42.singletState * run 1).trace.re := by sorry

end BindingEntChannels
