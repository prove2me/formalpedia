-- Prove2me | Theorems.Thm_AffDisp4n_lemma_4_2
-- name    : AffDisp4n.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:04:27.336775+00:00
-- url     : https://prove2.me/theorems/51ea15ee-dc30-4067-b670-a0e4c37470d6
-- title:
--   Lemma 4.2 (existence clause; polynomial-time clause: lemma_4_2_time) — a constant subspace, or progress with $\Delta W \le 10\,\Delta a$
-- statement:
--   Let $C_0$ be a $B_2$-circuit on $n$ inputs, let $d \ge 0$, and let $\sigma$ be a state valid for $C_0$ with $a > d$. Then one of the following holds.
--
--   1. There are a nonempty affine subspace $S \subseteq \mathbb F_2^n$ of dimension at least $d$ and a constant $b \in \mathbb F_2$ with $C_0(x) = b$ for all $x \in S$.
--   2. There is a state $\sigma'$, valid for the same $C_0$, with
--   $$
--   m' + s' < m + s, \qquad \Delta a \in \{0, -1\}, \qquad \Delta W \le 10\,\Delta a .
--   $$
--
--   Applying the lemma repeatedly from the initial state, where $W \le |C_0| + 6n$, gives Theorem 4.1. A circuit with fewer than $4n - 10d$ gates is constant on an affine subspace of dimension at least $d$.
--
--   **Formalization Note** This item is the existence clause; "in deterministic polynomial time" is the companion item `AffDisp4n.lemma_4_2_time`. "The current state" is any state valid for $C_0$. The quantities $a$, $W$ and their differences are integers.
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - reading: in deterministic polynomial time, the gate elimination algorithm either constructs S and b, or transforms the current state into a new state → ∃ S, b with C₀ ≡ b on S, or ∃ σ′ valid for C₀ with the stated changes; the polynomial-time clause is the companion item AffDisp4n.lemma_4_2_time; reason: the existence clause needs no machine or encoding, and it is the part Theorem 4.1's lower bound uses; the title names the companion
--   - encoding: an affine subspace S ⊆ 𝔽₂ⁿ of dimension at least d; ∆a ∈ {0, −1}, ∆W ≤ 10∆a → a nonempty AffineSubspace with d ≤ finrank S.direction; σ′.a = σ.a ∨ σ′.a = σ.a − 1 and (σ′.W : ℤ) − σ.W ≤ 10(σ′.a − σ.a); reason: Mathlib affine subspaces; integer arithmetic
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4, p.21, Lemma 4.2 (proof p.25)

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_gateVal
import Definitions.Def_AffDisp4n_Acyclic_eval
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_AffDisp4n_Acyclic_mapInput
import Definitions.Def_AffDisp4n_Acyclic_Reads
import Definitions.Def_AffDisp4n_PairsDisjoint
import Definitions.Def_AffDisp4n_Z
import Definitions.Def_AffDisp4n_IsAffineOp
import Definitions.Def_AffDisp4n_IsAndOp
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_Phi
import Definitions.Def_AffDisp4n_State_eval
import Definitions.Def_AffDisp4n_State_Valid
import Definitions.Def_AffDisp4n_State_s
import Definitions.Def_AffDisp4n_State_q
import Definitions.Def_AffDisp4n_State_a
import Definitions.Def_AffDisp4n_State_IsPaired
import Definitions.Def_AffDisp4n_State_deg
import Definitions.Def_AffDisp4n_State_W
import Definitions.Def_AffDisp4n_State_D1Applicable
import Definitions.Def_AffDisp4n_State_D2Applicable
import Definitions.Def_AffDisp4n_State_D3Applicable
import Definitions.Def_AffDisp4n_State_D4Applicable
import Definitions.Def_AffDisp4n_State_AffineMovable
import Definitions.Def_AffDisp4n_State_Reduced
import Definitions.Def_AffDisp4n_State_OutputSimple
import Definitions.Def_AffDisp4n_State_Case1Applicable
import Definitions.Def_AffDisp4n_State_Case2Applicable
import Definitions.Def_AffDisp4n_State_Case3Applicable

namespace AffDisp4n

/-- **Lemma 4.2** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), p.21; proof p.25). "Suppose that a > d. Then … the gate elimination algorithm
either constructs an affine subspace S ⊆ 𝔽₂ⁿ of dimension at least d and a constant b ∈ 𝔽₂ such that
C₀(x) = b for all x ∈ S, or transforms the current state into a new state such that m′ + s′ < m + s,
∆a ∈ {0, −1}, and ∆W ≤ 10∆a." For every state valid for the original circuit `C₀` with `a > d`: either
`C₀` is constant on some nonempty affine subspace of `𝔽₂ⁿ` of dimension at least `d`, or some state
valid for the same `C₀` satisfies `m′ + s′ < m + s`, `a′ − a ∈ {0, −1}` and `W′ − W ≤ 10 (a′ − a)`.

**Formalization Note** This item is the existence clause of the lemma; "in deterministic polynomial
time" is the companion item `lemma_4_2_time`. "The current state" is any state valid for `C₀` (`State.Valid`): the
proof uses only these invariants. `a`, `W` and the differences are integers. -/
theorem lemma_4_2 {n : ℕ} (C₀ : Circuit n) (d : ℕ) (σ : State n) (hσ : σ.Valid C₀)
    (had : (d : ℤ) < σ.a) :
    (∃ S : AffineSubspace (ZMod 2) (Fin n → ZMod 2), (S : Set (Fin n → ZMod 2)).Nonempty ∧
        d ≤ Module.finrank (ZMod 2) S.direction ∧ ∃ b : ZMod 2, ∀ x ∈ S, C₀.eval x = b) ∨
      ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.m + σ'.s < σ.m + σ.s ∧ (σ'.a = σ.a ∨ σ'.a = σ.a - 1) ∧
        (σ'.W : ℤ) - σ.W ≤ 10 * (σ'.a - σ.a) := by sorry

end AffDisp4n
