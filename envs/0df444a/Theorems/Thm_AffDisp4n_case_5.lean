-- Prove2me | Theorems.Thm_AffDisp4n_case_5
-- name    : AffDisp4n.case_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:04:17.309537+00:00
-- url     : https://prove2.me/theorems/85c785c5-49cf-4f66-8fcc-a75a01688848
-- title:
--   §4.3 Case 5 — an input of the minimal AND is paired: $\Delta a = -1$, $\Delta W \le -12$ ($k=1$) or $\le -10$ ($k=2$)
-- statement:
--   Let $\sigma$ be a state valid for the original circuit $C_0$ at the end of §4.2. That is, no deletion (D1)–(D4) or move of an affine gate applies, none of Cases 1–3 applies, the first gate $G$ of the acyclic part is AND-type with inputs the parameters $x$ and $y$, and $G$ is not the output. Let $k \in \{1, 2\}$ be the number of paired inputs of $G$.
--
--   1. If $k = 1$, there is a state $\sigma'$ valid for $C_0$ with $\Delta m = -2$, $\Delta q = -1$, $\Delta s \le -2$, $\Delta a = -1$ and $\Delta W \le -12$.
--   2. If $k = 2$, there is a state $\sigma'$ valid for $C_0$ with $\Delta m = -3$, $\Delta q = -2$, $\Delta s \le -2$, $\Delta a = -1$ and $\Delta W \le -10$.
--
--   In the paper, (PF) fixes the partners to $0$ and (UF) fixes $x$ (or the unpaired input) so that $G$ is constant. Then $G$ and the unique child of a partner are deleted by (D1).
--
--   **Formalization Note** The hypotheses are written out as in Case 4.
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - generalization: standing assumption a > d of §4.2–§4.3 → no assumption on a; reason: the step does not use a > d; the statement with it is a special case
--   - reading: the paragraph describes an operation and its effect (PF on the partners, UF on x, delete G and H_r; k = 1: ∆m = −2, ∆q = −1, ∆s ≤ −2, ∆W ≤ −12; k = 2: ∆m = −3, ∆q = −2, ∆s ≤ −2, ∆W ≤ −10) → there is a state σ′ valid for the same C₀ with these changes of m, q, s and W; reason: the proof of Lemma 4.2 uses exactly the existence of such a successor with these changes; Δa follows from Δm and Δq
--   - encoding: the state reached at the end of §4.2 with G not the output → hypotheses Reduced, ¬ Case 1–3, gate 0 AND-type with inputs the parameters x and y, output ≠ gate 0; reason: the paper's assumptions at this point, written out
--   - encoding: without loss of generality x is unpaired and y is paired (k = 1) → both orders: (x paired ∧ y unpaired) ∨ (x unpaired ∧ y paired); reason: the two orders are symmetric; stating both removes the WLOG
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4.3, p.25, "Case 5: at least one input of G is paired"

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

/-- **Case 5: at least one input of the minimal AND `G` is paired** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4.3, p.25). Let `k ∈ {1, 2}`
be the number of paired inputs of `G`.
1. `k = 1` (one input unpaired, the other paired with partner `r`): (PF) fixes `r` to `0` and (UF) fixes
   the unpaired input so that `G` is constant; `G` and the unique child `H_r` of `r` are deleted:
   "∆m = −2 …, ∆s ≤ −2 …, ∆q = −1 …, and ∆a = ∆m − ∆q = −1. This gives ∆W ≤ −2 − 4 − 6 = −12."
2. `k = 2` (partners `r_x`, `r_y`): (PF) twice, then (UF) fixes `x`; `G` and `H_{r_x}` are deleted:
   "∆m = −3 …, ∆s ≤ −2 …, ∆q = −2 …, and ∆a = ∆m − ∆q = −1. This gives ∆W ≤ −2 − 8 = −10."
Each successor is valid for the same original circuit `C₀`.

**Formalization Note** The hypotheses are the state reached at the end of §4.2: no preliminary reduction applies
(`State.Reduced`, not Cases 1–3), the minimal AND `G` is the first gate, it is AND-type, it reads the
parameters `x` and `y`, and `G` is not the output (otherwise Lemma 2.2 applies, p.24). The paper's
standing assumption `a > d` is not used by this step and is omitted. The paper's "without loss of generality … x is unpaired and y is
paired" is stated for both orders. -/
theorem case_5 {n : ℕ} (C₀ : Circuit n) (σ : State n) (hσ : σ.Valid C₀) (hred : σ.Reduced)
    (h1 : ¬ σ.Case1Applicable) (h2 : ¬ σ.Case2Applicable) (h3 : ¬ σ.Case3Applicable)
    (h : 0 < σ.circ.size) (hand : IsAndOp (σ.circ.op ⟨0, h⟩)) (x y : Fin σ.m)
    (hx : σ.circ.in₁ ⟨0, h⟩ = .input (.inl x)) (hy : σ.circ.in₂ ⟨0, h⟩ = .input (.inl y))
    (hGout : σ.circ.out ≠ .gate ⟨0, h⟩) :
    ((σ.IsPaired x ∧ ¬ σ.IsPaired y) ∨ (¬ σ.IsPaired x ∧ σ.IsPaired y) →
      ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.m + 2 = σ.m ∧ σ'.q + 1 = σ.q ∧ σ'.s + 2 ≤ σ.s ∧
        σ'.W + 12 ≤ σ.W) ∧
    (σ.IsPaired x ∧ σ.IsPaired y →
      ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.m + 3 = σ.m ∧ σ'.q + 2 = σ.q ∧ σ'.s + 2 ≤ σ.s ∧
        σ'.W + 10 ≤ σ.W) := by sorry

end AffDisp4n
