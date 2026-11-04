-- Prove2me | Theorems.Thm_BaconThesis_ExchangeUniv_eq_9_7_9_8
-- name    : BaconThesis.ExchangeUniv.eq_9_7_9_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:50.358396+00:00
-- url     : https://prove2.me/theorems/53911987-ecf4-4794-8981-0a77ff7f79c7
-- title:
--   Eqs. (9.6)–(9.8) — the exchange $E_{ij}=\tfrac12(I+\vec\sigma^{(i)}\cdot\vec\sigma^{(j)})$ commutes with every collective spin
-- statement:
--   Let $n$ qubits be given and let $k\neq l$ be two of them.
--
--   1. (9.5)–(9.6) For real $h_{33},h_{12},h_{11}$, the two-qubit operator
--   $$
--   H^{(kl)}(h_{33},h_{12},h_{11})=h_{33}\sigma^{(k)}_z\sigma^{(l)}_z+h_{12}\big(\sigma^{(k)}_x\sigma^{(l)}_y-\sigma^{(k)}_y\sigma^{(l)}_x\big)+h_{11}\big(\sigma^{(k)}_x\sigma^{(l)}_x+\sigma^{(k)}_y\sigma^{(l)}_y\big)
--   $$
--   commutes with $S^{[n]}_x$ if and only if $h_{11}=h_{33}$ and $h_{12}=0$.
--   2. (9.7) For every real $h$, the Heisenberg operator $h\,\vec\sigma^{(k)}\cdot\vec\sigma^{(l)}=h\sum_{\beta}\sigma^{(k)}_\beta\sigma^{(l)}_\beta$ commutes with $S^{[n]}_x,S^{[n]}_y,S^{[n]}_z$.
--   3. (9.8) The exchange of qubits $k$ and $l$ is
--   $$
--   E_{kl}=\tfrac12\big(I+\sigma^{(k)}_x\sigma^{(l)}_x+\sigma^{(k)}_y\sigma^{(l)}_y+\sigma^{(k)}_z\sigma^{(l)}_z\big).
--   $$
--   4. $E_{kl}$ commutes with $S^{[n]}_x,S^{[n]}_y,S^{[n]}_z$.
--
--   So the exchange interaction lies in the commutant of the strong collective decoherence algebra and preserves every DFS; it is the only generator used in the mission.
--
--   **Formalization Note** Qubits are indexed from $0$. $E_{kl}$ is defined as the permutation matrix of the transposition of qubits $k,l$, so clause 3 is the content of (9.8), and its two-qubit matrix is the $4\times4$ matrix printed there.
--
--   Differences from the source:
--   - reading: (9.6) "vanishes only if h11 = h33 and h12 = 0" → an iff; reason: the page goes on to conclude that (9.7), the case h11 = h33, h12 = 0, commutes, which is the converse direction
--   - encoding: E_ij given by its 4×4 matrix on qubits i, j and the swap rule → the permutation matrix of the transposition (k l) on n-qubit bit strings; reason: the same operator
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §9.1.2, eqs. (9.5)–(9.8), p.126 (PDF p.143)

import Mathlib
import Definitions.Def_BaconThesis_ExchangeUniv_pauli
import Definitions.Def_BaconThesis_Collective_onQubit
import Definitions.Def_BaconThesis_ExchangeUniv_collS
import Definitions.Def_BaconThesis_Collective_exchange

open scoped Matrix

namespace BaconThesis.ExchangeUniv

/-- **(9.6)–(9.8): the two-qubit operators commuting with every collective spin are the
BaconThesis.Collective.exchange, and `E_ij = ½(I + σ^(i)·σ^(j))`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §9.1.2, (9.5)–(9.8), p.126 (PDF p.143).

For `n` qubits and two distinct qubits `k ≠ l`:
1. ((9.5)–(9.6)) for real `h₃₃, h₁₂, h₁₁`, the weak-commutant operator
   `H = h₃₃ σ_z^k σ_z^l + h₁₂(σ_x^k σ_y^l − σ_y^k σ_x^l) + h₁₁(σ_x^k σ_x^l + σ_y^k σ_y^l)` commutes
   with `S_x^[n]` iff `h₁₁ = h₃₃` and `h₁₂ = 0`;
2. ((9.7)) `H = h(σ_x^k σ_x^l + σ_y^k σ_y^l + σ_z^k σ_z^l)` commutes with `S_x, S_y, S_z` for
   every real `h`;
3. ((9.8)) the BaconThesis.Collective.exchange (swap) of qubits `k` and `l` equals `½(I + σ^k·σ^l)`;
4. the BaconThesis.Collective.exchange commutes with `S_x^[n], S_y^[n], S_z^[n]`.

**Formalization Note.** Qubits are indexed from `0`; `α = 0, 1, 2` is `x, y, z`. `exchange k l`
is the permutation matrix of the transposition of qubits `k` and `l`, so its matrix on the two
qubits is the `4 × 4` matrix of (9.8); the "global phase I operator and scaling" of p.126 is the
passage from clause 2 (with `h = 1/2`) to clause 3. -/
theorem eq_9_7_9_8 (n : ℕ) (k l : Fin n) (hkl : k ≠ l) :
    (∀ h₃₃ h₁₂ h₁₁ : ℝ,
      Commute (collS n 0)
        ((h₃₃ : ℂ) • (BaconThesis.Collective.onQubit k (pauli 2) * BaconThesis.Collective.onQubit l (pauli 2)) +
          (h₁₂ : ℂ) • (BaconThesis.Collective.onQubit k (pauli 0) * BaconThesis.Collective.onQubit l (pauli 1) -
            BaconThesis.Collective.onQubit k (pauli 1) * BaconThesis.Collective.onQubit l (pauli 0)) +
          (h₁₁ : ℂ) • (BaconThesis.Collective.onQubit k (pauli 0) * BaconThesis.Collective.onQubit l (pauli 0) +
            BaconThesis.Collective.onQubit k (pauli 1) * BaconThesis.Collective.onQubit l (pauli 1))) ↔
        h₁₁ = h₃₃ ∧ h₁₂ = 0) ∧
    (∀ (h : ℝ) (α : Fin 3),
      Commute ((h : ℂ) • ∑ β : Fin 3, BaconThesis.Collective.onQubit k (pauli β) * BaconThesis.Collective.onQubit l (pauli β)) (collS n α)) ∧
    BaconThesis.Collective.exchange k l = (1 / 2 : ℂ) • (1 + ∑ β : Fin 3, BaconThesis.Collective.onQubit k (pauli β) * BaconThesis.Collective.onQubit l (pauli β)) ∧
    ∀ α : Fin 3, Commute (BaconThesis.Collective.exchange k l) (collS n α) := by sorry

end BaconThesis.ExchangeUniv
