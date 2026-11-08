-- Prove2me | Theorems.Thm_AffDisp4n_lemma_4_2_time
-- name    : AffDisp4n.lemma_4_2_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:03:16.17121+00:00
-- url     : https://prove2.me/theorems/f0ff87c3-de3a-4879-8920-6383c0acc618
-- title:
--   Lemma 4.2, polynomial-time clause — one iteration of gate elimination on a machine (existence clause: lemma_4_2)
-- statement:
--   There is one polynomial-time machine that takes a state and writes either a point $x_0$, linearly independent vectors $B$ and a bit $b$, or a new state $\sigma'$, such that the following holds for every $B_2$-circuit $C_0$, every $d \ge 0$ and every state $\sigma$ valid for $C_0$ with $a > d$. In the first case, $|B| \ge d$ and $C_0(x) = b$ for all $x \in x_0 + \operatorname{span} B$. In the second case, $\sigma'$ is valid for the same $C_0$ and
--   $$
--   m' + s' < m + s, \qquad \Delta a \in \{0, -1\}, \qquad \Delta W \le 10\,\Delta a .
--   $$
--
--   This is the polynomial-time clause of Lemma 4.2. The companion item `AffDisp4n.lemma_4_2` is the existence clause, the part the lower bound uses.
--
--   **Formalization Note** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime`, as in the published `PvsNP.P`. The quantities $a$, $W$ and their differences are integers.
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - generalization: the algorithm runs under the hypothesis a > d, for a circuit C₀ → one machine, chosen before C₀ and d, that receives only the state; reason: each iteration of the paper reads only the state (the case analysis pp.21–25 never reads d or C₀); for given C₀ and d it is the printed statement
--   - reading: the gate elimination algorithm → some polynomial-time machine with the printed properties; reason: the properties are the content of the lemma; the steps of the algorithm are its proof, and the milestones of §3–§4 state them
--   - encoding: in deterministic polynomial time → Nonempty (Turing.TM2ComputableInPolyTime encState (fun l => l) F); reason: the paper fixes no machine or encoding; this is the machine of the published PvsNP.P, and the input length is polynomial in n + m + r and the number of gates, and at least each of them
--   - encoding: constructs an affine subspace S ⊆ 𝔽₂ⁿ of dimension at least d and a constant b, or transforms the current state into a new state → the output is tag false with a point x₀, a linearly independent list B and a bit b, with d ≤ |B| and S = x₀ + span B, or tag true with the words of σ′; reason: the paper represents subspaces by a point and a basis (p.17), and the dimension of x₀ + span B is |B|
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4, p.21, Lemma 4.2 (proof p.25)

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_gateVal
import Definitions.Def_AffDisp4n_Acyclic_eval
import Definitions.Def_AffDisp4n_Acyclic_tokens
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_eval
import Definitions.Def_AffDisp4n_State_Valid
import Definitions.Def_AffDisp4n_State_s
import Definitions.Def_AffDisp4n_State_q
import Definitions.Def_AffDisp4n_State_a
import Definitions.Def_AffDisp4n_State_W
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_AffDisp4n_vecWord
import Definitions.Def_AffDisp4n_pointBasisSubspace
import Definitions.Def_AffDisp4n_encState

namespace AffDisp4n

/-- **Lemma 4.2, polynomial-time clause** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), p.21; proof p.25): "Suppose that a > d. Then, in deterministic polynomial time, the gate elimination algorithm either
constructs an affine subspace S ⊆ 𝔽₂ⁿ of dimension at least d and a constant b ∈ 𝔽₂ such that C₀(x⃗) = b for
all x⃗ ∈ S, or transforms the current state into a new state such that m′ + s′ < m + s, ∆a ∈ {0, −1}, and
∆W ≤ 10∆a." One polynomial-time machine takes a state and writes either a point, a basis and a bit (tag
`false`) or a new state (tag `true`), such that for every state valid for an original circuit `C₀` with
`a > d`, the output has the printed properties. The existence clause alone is the companion item `lemma_4_2`.

**Formalization Note** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime`, as in the published
`PvsNP.P`. The machine receives neither `C₀` nor `d`: the paper's iteration reads only the state. The
encodings are `encState` and `LowErrExt.encWords`. `a`, `W` and the differences are integers. -/
theorem lemma_4_2_time :
    ∃ F : (Σ n, State n) → List (Fin 3),
      Nonempty (Turing.TM2ComputableInPolyTime encState (fun l : List (Fin 3) => l) F) ∧
      ∀ (n : ℕ) (C₀ : Circuit n) (d : ℕ) (σ : State n), σ.Valid C₀ → (d : ℤ) < σ.a →
        (∃ (x₀ : Fin n → ZMod 2) (B : List (Fin n → ZMod 2)) (b : ZMod 2),
            F ⟨n, σ⟩ = LowErrExt.encWords ([[false]] ++ subspaceTokens x₀ B b) ∧
            LinearIndependent (ZMod 2) (fun i : Fin B.length => B.get i) ∧
            d ≤ B.length ∧ ∀ x ∈ pointBasisSubspace x₀ B, C₀.eval x = b) ∨
          ∃ σ' : State n, F ⟨n, σ⟩ = LowErrExt.encWords ([[true]] ++ σ'.tokens) ∧ σ'.Valid C₀ ∧
            σ'.m + σ'.s < σ.m + σ.s ∧ (σ'.a = σ.a ∨ σ'.a = σ.a - 1) ∧
            (σ'.W : ℤ) - σ.W ≤ 10 * (σ'.a - σ.a) := by sorry

end AffDisp4n
