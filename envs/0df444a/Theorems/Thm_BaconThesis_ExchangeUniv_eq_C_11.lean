-- Prove2me | Theorems.Thm_BaconThesis_ExchangeUniv_eq_C_11
-- name    : BaconThesis.ExchangeUniv.eq_C_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:53.828484+00:00
-- url     : https://prove2.me/theorems/a5a6eb3c-cae3-4b10-9cf5-61e302f17098
-- title:
--   Eq. (C.11) with (D.8) (corrected: $\theta_J$, not $\theta_{J+1}$) — exchange of the last two qubits on the TT, BT, TB, BB states
-- statement:
--   Let $n=m+2$ qubits, $J\ge0$, and $\theta_J=\arctan\big(2\sqrt{J(J+1)}\big)$, so that $\cos\theta_J=1/(2J+1)$. Write $|{\uparrow}\rangle=|\tfrac12,\tfrac12\rangle$, $|{\downarrow}\rangle=|\tfrac12,-\tfrac12\rangle$ for the states of qubits $n-1$ and $n$, and $S_-=S^{[m]}_x-iS^{[m]}_y$ on the first $m$ qubits. For vectors $u,v,w$ of the first $m$ qubits put
--   $$
--   u'=\tfrac{1}{\sqrt{2J}}S_-u,\qquad v'=\tfrac{1}{\sqrt{2J+2}}S_-v,\qquad v''=\tfrac{1}{\sqrt{2(2J+1)}}S_-v',
--   $$
--   and define, as in (D.8),
--   $$
--   \begin{aligned}
--   |TT\rangle&=\sqrt{\tfrac{2J+1}{2J+3}}\,v|{\downarrow\downarrow}\rangle-\sqrt{\tfrac{2J+1}{(2J+2)(2J+3)}}\,v'\big(|{\uparrow\downarrow}\rangle+|{\downarrow\uparrow}\rangle\big)+\sqrt{\tfrac{2}{(2J+2)(2J+3)}}\,v''|{\uparrow\uparrow}\rangle,\\
--   |BT\rangle&=-\sqrt{\tfrac{2J+1}{2J+2}}\,u|{\uparrow\downarrow}\rangle+\tfrac{1}{\sqrt{(2J+2)(2J+1)}}\,u|{\downarrow\uparrow}\rangle+\sqrt{\tfrac{2J}{(2J+1)(2J+2)}}\,u'|{\uparrow\uparrow}\rangle,\\
--   |TB\rangle&=-\sqrt{\tfrac{2J}{2J+1}}\,u|{\downarrow\uparrow}\rangle+\tfrac1{\sqrt{2J+1}}\,u'|{\uparrow\uparrow}\rangle,\qquad |BB\rangle=w|{\uparrow\uparrow}\rangle .
--   \end{aligned}
--   $$
--   Then the exchange $E_{n-1,n}$ of the last two qubits satisfies
--   $$
--   E|TT\rangle=|TT\rangle,\quad E|BT\rangle=-\cos\theta_J|BT\rangle+\sin\theta_J|TB\rangle,\quad E|TB\rangle=\sin\theta_J|BT\rangle+\cos\theta_J|TB\rangle,\quad E|BB\rangle=|BB\rangle;
--   $$
--   that is, in the basis $TT,BT,TB,BB$,
--   $$
--   E_{n,n-1}=\begin{pmatrix}1&0&0&0\\0&-\cos\theta_J&\sin\theta_J&0\\0&\sin\theta_J&\cos\theta_J&0\\0&0&0&1\end{pmatrix}.
--   $$
--   In the book $u,v,w$ are the maximal-$m$ path states $|J_1,\dots,J_{n-3},J';m=J'\rangle$ of the first $n-2$ qubits with $J'=J$, $J+1$, $J-1$, and the four vectors are the maximal-$m$ TT, BT, TB, BB states of $\mathrm{DFS}_n(J)$. Exchange mixes each BT-state with its TB partner and fixes the TT- and BB-states, which is the step that lets the induction of Appendix C pass between DFSs.
--
--   The printed (C.11) has $\theta_{J+1}$ in the middle block; the matrix (C.12) on the next page has $\theta_J$, which is correct. For $n=4$, $J=1$ (so $u=|{\uparrow\uparrow}\rangle$ on two qubits), $\langle BT|E|BT\rangle=-\tfrac13=-\cos\theta_1$, while $-\cos\theta_2=-\tfrac15$.
--
--   **Formalization Note** Qubits $n-1,n$ are the indices $m,m+1$; spin up is $|0\rangle$. Since $E_{n-1,n}$ acts only on the last two qubits, the identities hold for all vectors $u,v,w$, not only for the path states. At $J=0$ there is no TB-state and the formula gives the zero vector.
--
--   Differences from the source:
--   - correction: (C.11) middle block −cos(θ_{J+1}), sin(θ_{J+1}), cos(θ_{J+1}) → θ_J; reason: for n = 4, J = 1, u = |↑↑⟩, the BT-state of (D.8) has ⟨BT|E_{4,3}|BT⟩ = −1/3 = −cos θ_1 ≠ −cos θ_2 = −1/5; the book's (C.12) uses θ_J
--   - generalization: the maximal-m path states |J_1, …, J_{n−3}, J'; m = J'⟩ → arbitrary vectors u, v, w of the first n − 2 qubits; reason: E_{n−1,n} acts only on the last two qubits; specializes to the path states
--   - encoding: the TB-state at J = 0 (which does not exist) → the zero vector; reason: (√0)⁻¹ = 0 in Lean; the clause is then trivially true and the book excludes the case
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §C.2, eqs. (C.9)–(C.11), p.249 (PDF p.266); states (D.8), pp.255–256 (PDF pp.272–273); (C.12), p.250 (PDF p.267)

import Mathlib
import Definitions.Def_BaconThesis_ExchangeUniv_collS
import Definitions.Def_BaconThesis_Collective_exchange

open scoped Matrix

namespace BaconThesis.ExchangeUniv

/-- **(C.11) with (D.8), corrected (θ_J, not θ_{J+1}): the BaconThesis.Collective.exchange of the last two qubits on the
TT, BT, TB and BB states.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §C.2, (C.9)–(C.11), p.249 (PDF p.266), with the states of (D.8), pp.255–256
(PDF pp.272–273), and (C.12), p.250 (PDF p.267).

Let `n = m + 2`, `J ≥ 0` and `θ_J = arctan(2√(J(J+1)))` (so `cos θ_J = 1/(2J+1)`). For vectors
`u, v, w` of the first `m` qubits put `u' = S_−u/√(2J)`, `v' = S_−v/√(2J+2)`,
`v'' = S_−v'/√(2(2J+1))` (`S_− = S_x − iS_y`, Condon–Shortley lowering), and, with `|↑⟩ = |½,½⟩`,
`|↓⟩ = |½,−½⟩` on qubits `n−1, n` (D.8):
* `|TT⟩ = √((2J+1)/(2J+3)) v|↓↓⟩ − √((2J+1)/((2J+2)(2J+3))) v'(|↑↓⟩ + |↓↑⟩) + √(2/((2J+2)(2J+3))) v''|↑↑⟩`;
* `|BT⟩ = −√((2J+1)/(2J+2)) u|↑↓⟩ + (2J+2)^{−1/2}(2J+1)^{−1/2} u|↓↑⟩ + √(2J/((2J+1)(2J+2))) u'|↑↑⟩`;
* `|TB⟩ = −√(2J/(2J+1)) u|↓↑⟩ + (2J+1)^{−1/2} u'|↑↑⟩`;
* `|BB⟩ = w|↑↑⟩`.
Then the BaconThesis.Collective.exchange `E_{n−1,n}` of the last two qubits satisfies
`E|TT⟩ = |TT⟩`, `E|BT⟩ = −cos θ_J |BT⟩ + sin θ_J |TB⟩`, `E|TB⟩ = sin θ_J |BT⟩ + cos θ_J |TB⟩`,
`E|BB⟩ = |BB⟩`: the matrix (C.11) in the basis `TT, BT, TB, BB`, with `θ_J` in the middle block.

The printed (C.11) has `θ_{J+1}`; the (C.12) on the next page has `θ_J`, which is the correct one
(at `J = 1`, `⟨BT|E|BT⟩ = −1/3 = −cos θ_1`, while `cos θ_2 = 1/5`).

**Formalization Note.** Qubits `n−1, n` of the book are indices `m, m+1` of `Fin (m+2)`
(`Fin.castSucc (Fin.last m)` and `Fin.last (m+1)`); the first `m` qubits are
`x ∘ Fin.castSucc ∘ Fin.castSucc`. Spin up `|½,½⟩` is `|0⟩` (`σ_z|0⟩ = |0⟩`). In the book `u`, `v`,
`w` are the maximal-`m` path states `|J₁,…,J_{n−3}, J'; m = J'⟩` of the first `n−2` qubits with
`J' = J, J+1, J−1`; the identity holds for every vector `u, v, w`, since `E` acts only on the last
two qubits. At `J = 0` there is no TB-state and the Lean `|TB⟩` is `0` (`(√0)⁻¹ = 0`). -/
theorem eq_C_11 (m : ℕ) (J : ℝ) (hJ : 0 ≤ J) (u v w : (Fin m → Fin 2) → ℂ) :
    let a : Fin (m + 2) := Fin.castSucc (Fin.last m)
    let b : Fin (m + 2) := Fin.last (m + 1)
    let ext : ((Fin m → Fin 2) → ℂ) → Fin 2 → Fin 2 → (Fin (m + 2) → Fin 2) → ℂ :=
      fun y s t x => if x a = s ∧ x b = t then y (fun k => x (Fin.castSucc (Fin.castSucc k))) else 0
    let Sm : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ := collS m 0 - Complex.I • collS m 1
    let c : ℝ → ℂ := fun r => ((Real.sqrt r : ℝ) : ℂ)
    let u' := (c (2 * J))⁻¹ • (Sm *ᵥ u)
    let v' := (c (2 * J + 2))⁻¹ • (Sm *ᵥ v)
    let v'' := (c (2 * (2 * J + 1)))⁻¹ • (Sm *ᵥ v')
    let TT := c ((2 * J + 1) / (2 * J + 3)) • ext v 1 1
      - c ((2 * J + 1) / ((2 * J + 2) * (2 * J + 3))) • (ext v' 0 1 + ext v' 1 0)
      + c (2 / ((2 * J + 2) * (2 * J + 3))) • ext v'' 0 0
    let BT := -c ((2 * J + 1) / (2 * J + 2)) • ext u 0 1
      + (c ((2 * J + 2) * (2 * J + 1)))⁻¹ • ext u 1 0
      + c (2 * J / ((2 * J + 1) * (2 * J + 2))) • ext u' 0 0
    let TB := -c (2 * J / (2 * J + 1)) • ext u 1 0 + (c (2 * J + 1))⁻¹ • ext u' 0 0
    let BB := ext w 0 0
    let θ := Real.arctan (2 * Real.sqrt (J * (J + 1)))
    let E := BaconThesis.Collective.exchange a b
    E *ᵥ TT = TT ∧
    E *ᵥ BT = (-(Real.cos θ : ℂ)) • BT + (Real.sin θ : ℂ) • TB ∧
    E *ᵥ TB = (Real.sin θ : ℂ) • BT + (Real.cos θ : ℂ) • TB ∧
    E *ᵥ BB = BB := by sorry

end BaconThesis.ExchangeUniv
