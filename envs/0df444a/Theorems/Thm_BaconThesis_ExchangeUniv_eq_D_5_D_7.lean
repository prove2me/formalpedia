-- Prove2me | Theorems.Thm_BaconThesis_ExchangeUniv_eq_D_5_D_7
-- name    : BaconThesis.ExchangeUniv.eq_D_5_D_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:57.897273+00:00
-- url     : https://prove2.me/theorems/0ea0e3c8-41ae-4fb1-9c15-6aa9c894b71f
-- title:
--   Eqs. (D.5)–(D.7) — the coefficients $\alpha=-\sqrt{\tfrac{2J+1}{2J+2}}$, $\beta=\tfrac1{\sqrt{2J+2}}$ of the maximal-$m$ T-state
-- statement:
--   Let $J\ge0$ and let $|T_+\rangle$ be a unit vector of $m$ qubits with
--   $$
--   S^{[m]}_z|T_+\rangle=(J+\tfrac12)|T_+\rangle,\qquad S^{[m]}_+|T_+\rangle=0,
--   $$
--   where $S_\pm=S_x\pm iS_y$; so $|T_+\rangle$ is a maximal-$m$ state of total spin $J+\tfrac12$. Put $|T_-\rangle=(2J+1)^{-1/2}S^{[m]}_-|T_+\rangle$ and, appending one qubit,
--   $$
--   |\psi\rangle=\alpha|T_+\rangle|\tfrac12,-\tfrac12\rangle+\beta|T_-\rangle|\tfrac12,\tfrac12\rangle\qquad(\alpha,\beta\in\mathbb C).
--   $$
--   Then, with $S_+=S^{[m+1]}_+$:
--
--   1. (D.6) $S_+|\psi\rangle=0$ if and only if $\alpha+\sqrt{2J+1}\,\beta=0$;
--   2. (D.7) $S_+|\psi\rangle=0$ and $\langle\psi|\psi\rangle=1$ if and only if there is a phase $c$, $|c|=1$, with
--   $$
--   \alpha=-c\sqrt{\frac{2J+1}{2J+2}},\qquad \beta=\frac{c}{\sqrt{2J+2}} .
--   $$
--
--   These are the coefficients of the maximal-$m$ T-state of $\mathrm{DFS}_{m+1}(J)$, the input to the TT, BT, TB, BB states used in the inductive proof.
--
--   **Formalization Note** The appended qubit is the last one; spin up $|\tfrac12,\tfrac12\rangle$ is $|0\rangle$. The relative phase of $|T_-\rangle$ is that of the raising formula $J_+|j,m\rangle=[j(j+1)-m(m+1)]^{1/2}|j,m+1\rangle$ used on the page.
--
--   Differences from the source:
--   - generalization: |T₊⟩ the path state |J_1, …, J_{n−2}, J + 1/2; m = J + 1/2⟩ → any unit vector with S_z eigenvalue J + 1/2 annihilated by S_+; reason: the page's computation uses only these properties; specializes to the path states
--   - reading: "Application of S+ to Eq. (D.5) thus yields α + √(2J+1)β = 0" and "up to an arbitrary phase choice, α = …, β = …" → two iff statements, with the phase c, |c| = 1; reason: the page derives the coefficients from S_+|ψ⟩ = 0 and normalization, and the phase is the stated freedom
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Appendix D.1, eqs. (D.4)–(D.7), p.255 (PDF p.272)

import Mathlib
import Definitions.Def_BaconThesis_ExchangeUniv_collS

open scoped Matrix

namespace BaconThesis.ExchangeUniv

/-- **(D.5)–(D.7): the coefficients of the maximal-`m` T-state.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, Appendix D.1, (D.4)–(D.7), p.255 (PDF p.272).

Let `n = m + 1`, `J ≥ 0`, and let `|T₊⟩` be a unit vector of `m` qubits of total spin
`J + 1/2` with maximal `m`-value: `S_z^[m]|T₊⟩ = (J + ½)|T₊⟩` and `S_+^[m]|T₊⟩ = 0`, where
`S_± = S_x ± iS_y`. Put `|T₋⟩ = (2J + 1)^{−1/2} S_−^[m]|T₊⟩` (the state `|…, J + ½; J − ½⟩`) and
`|ψ⟩ = α|T₊⟩|½, −½⟩ + β|T₋⟩|½, ½⟩` (D.5), with the last qubit appended. Then
1. (D.6) `S_+^[n]|ψ⟩ = 0` iff `α + √(2J+1) β = 0`;
2. (D.7) `S_+^[n]|ψ⟩ = 0` and `⟨ψ|ψ⟩ = 1` iff, up to a phase `c` with `|c| = 1`,
   `α = −c√((2J+1)/(2J+2))` and `β = c/√(2J+2)`.

**Formalization Note.** The `n`-qubit basis is `Fin (m+1) → Fin 2`; the appended qubit is
`Fin.last m` and `Fin.init x` is the string of the first `m` qubits. Spin up `|½, ½⟩` is `|0⟩`
(`σ_z|0⟩ = |0⟩`), spin down is `|1⟩`. The relative phase of `|T₋⟩` is the one of the raising
formula `J_+|j, m⟩ = [j(j+1) − m(m+1)]^{1/2}|j, m+1⟩` used on p.255. `|T₊⟩` may be any such
highest-weight vector (the book's is one with a given path `J₁, …, J_{n−2}`). -/
theorem eq_D_5_D_7 (m : ℕ) (J : ℝ) (hJ : 0 ≤ J) (Tp : (Fin m → Fin 2) → ℂ)
    (hz : collS m 2 *ᵥ Tp = ((J + 1 / 2 : ℝ) : ℂ) • Tp)
    (hup : (collS m 0 + Complex.I • collS m 1) *ᵥ Tp = 0)
    (hnorm : star Tp ⬝ᵥ Tp = 1) (α β : ℂ) :
    let Tm : (Fin m → Fin 2) → ℂ :=
      (((Real.sqrt (2 * J + 1))⁻¹ : ℝ) : ℂ) • ((collS m 0 - Complex.I • collS m 1) *ᵥ Tp)
    let ψ : (Fin (m + 1) → Fin 2) → ℂ := fun x =>
      if x (Fin.last m) = 1 then α * Tp (Fin.init x) else β * Tm (Fin.init x)
    ((collS (m + 1) 0 + Complex.I • collS (m + 1) 1) *ᵥ ψ = 0 ↔
        α + (Real.sqrt (2 * J + 1) : ℂ) * β = 0) ∧
    ((collS (m + 1) 0 + Complex.I • collS (m + 1) 1) *ᵥ ψ = 0 ∧ star ψ ⬝ᵥ ψ = 1 ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧
        α = c * (-(Real.sqrt ((2 * J + 1) / (2 * J + 2)) : ℂ)) ∧
        β = c * ((1 / Real.sqrt (2 * J + 2) : ℝ) : ℂ)) := by sorry

end BaconThesis.ExchangeUniv
