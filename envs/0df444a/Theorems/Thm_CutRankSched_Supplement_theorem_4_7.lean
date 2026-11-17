-- Prove2me | Theorems.Thm_CutRankSched_Supplement_theorem_4_7
-- name    : CutRankSched.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:51:44.222668+00:00
-- url     : https://prove2.me/theorems/40484519-f529-4b72-894b-ed4e5ab19f76
-- title:
--   Theorem 4.7 — sound reverse compilation
-- statement:
--   Let a valid instance on the hardware graph $H$ carry the extracted trace $(\epsilon_1,p_1),\dots,(\epsilon_n,p_n)$ with connected exposure regions $T_i\subseteq H$ containing $\mathrm{supp}(p_i)$, and let $F$ be a final Clifford frame implementable on $H$ (Assumption 4.4): $F$ equals, up to a global phase, the unitary of a block of Clifford gates implementable on $H$. Let $\lambda:[n]\to[L]$ satisfy the constraints (2). Then there is a hardware circuit respecting $H$ with at most
--   $$
--   \max_i \lambda_i\ (\le L)
--   $$
--   non-Clifford rounds whose unitary equals $u\,F\,R_{\epsilon_n}(P(p_n))\cdots R_{\epsilon_1}(P(p_1))$ for some global phase $|u|=1$. (When $n=0$ the bound is $0$.)
--
--   The theorem shows that every schedule of Problem 3.2 is physically realizable with exactly the counted number of non-Clifford rounds, so the scheduling optimum is an achievable depth.
--
--   **Formalization Note** With 0-based layers the bound is $\max_i(\lambda_i+1)$.
--
--   Differences from the source:
--   - reading: Under Assumption 4.4 (single-qubit Cliffords, T/T† and two-qubit Cliffords along hardware edges; the final Clifford frame is implementable) → hardware circuits whose Clifford gates are H_q, S_q on any qubit and CNOT on edges of H, with T/T† layers on distinct qubits; hypothesis: F = v · U(B) for a Clifford block B on H, |v| = 1; reason: {H, S, CNOT on edges} generates the gates of Assumption 4.4 up to phase; implementable up to global phase is the source's phase convention
--   - reading: Assumption 4.4: each event is assigned its prescribed connected exposure region, and simultaneous exposure gadgets have disjoint vertex sets → the hypothesis I.Valid (connected T_i ⊆ H with supp(p_i) ⊆ V(T_i)); the conclusion does not separately constrain where the Clifford blocks act; reason: the theorem's conclusion is a hardware circuit with the same unitary and the round bound; the gadget sentence describes the construction of Lemmas 4.5–4.6
--   - reading: implementing the same unitary up to the tracked global phase → equal to u · F · R_{ε_n}(P(p_n)) ⋯ R_{ε_1}(P(p_1)) for some u with |u| = 1; reason: global phases are tracked or ignored consistently (p.6)
--   - encoding: at most max_i λ_i ≤ L non-Clifford rounds, λ : [n] → [L] → roundCount ≤ max_i (λ_i + 1) with λ : Fin n → Fin L (0 when n = 0); reason: 0-based layers; the sharper bound max_i λ_i is kept
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 4.7, p.7

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Instance_Valid
import Definitions.Def_CutRankSched_IsSchedule
import Definitions.Def_CutRankSched_Supplement_Gate
import Definitions.Def_CutRankSched_Supplement_circuitUnitary
import Definitions.Def_CutRankSched_Supplement_traceUnitary
import Definitions.Def_CutRankSched_Supplement_IsHwClifford
import Definitions.Def_CutRankSched_Supplement_HwCircuit

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- **Theorem 4.7 (Sound reverse compilation)** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 4.7, p.7). Under Assumption 4.4,
every feasible schedule `λ : [n] → [L]` for an extracted trace (4) can be compiled into a hardware
circuit implementing the same unitary up to the tracked global phase, with at most
`max_i λ_i ≤ L` non-Clifford rounds.

The extracted trace is `U = F R_{ε_n}(P(p_n)) ⋯ R_{ε_1}(P(p_1))` with the events of a valid
instance (signs `ε_i`, labels `p_i`, connected exposures `T_i ⊆ H` containing `supp(p_i)`), and
`F` implementable on `H` (Assumption 4.4): `F` equals, up to a global phase, the unitary of a
Clifford block on `H`. The conclusion is a hardware circuit on `H` with at most
`max_i λ_i` rounds (`max_i (λ_i + 1)` with 0-based layers, `0` when `n = 0`) and the same unitary
up to a global phase.

**Formalization Note** Single-qubit Cliffords anywhere, CNOT on hardware edges, T/T† layers on
distinct qubits (`HwCircuit.OnHardware`); Clifford gates cost nothing (`roundCount`). -/
theorem theorem_4_7 (I : Instance) (hI : I.Valid) (F : Op I.m)
    (hF : ∃ (B : List (Gate I.m)) (v : ℂ), (∀ g ∈ B, IsHwClifford I.H g) ∧ ‖v‖ = 1 ∧
      circuitUnitary B = v • F)
    (L : ℕ) (lam : Fin I.n → Fin L) (hlam : IsSchedule I L lam) :
    ∃ (c : HwCircuit I.m) (u : ℂ), c.OnHardware I.H ∧
      c.roundCount ≤ Finset.univ.sup (fun i => (lam i).val + 1) ∧ ‖u‖ = 1 ∧
      circuitUnitary c.gates =
        u • (F * traceUnitary (List.ofFn fun i : Fin I.n => (I.sign i, I.p i))) := by sorry

end Supplement

end CutRankSched
