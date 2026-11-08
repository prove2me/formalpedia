-- Prove2me | Theorems.Thm_AffDisp4n_case_4
-- name    : AffDisp4n.case_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:04:32.980069+00:00
-- url     : https://prove2.me/theorems/2306096b-fb95-455c-8620-4f202a7aa216
-- title:
--   §4.3 Case 4 — both inputs of the minimal AND are unpaired: $\Delta a = -1$, $\Delta W \le -10$
-- statement:
--   Let $\sigma$ be a state valid for the original circuit $C_0$ at the end of §4.2. That is, no deletion (D1)–(D4) or move of an affine gate applies, none of Cases 1–3 applies, the first gate $G$ of the acyclic part is AND-type with inputs the parameters $x$ and $y$, and $G$ is not the output. If $x$ and $y$ are both unpaired, there is a state $\sigma'$ valid for $C_0$ with
--   $$
--   \Delta m = 0, \quad \Delta q = 1, \quad \Delta s \le -2, \quad \Delta a = -1, \quad \Delta W \le -10 .
--   $$
--   In the paper, $x$ and $y$ are complemented if necessary so that $G = xy + \gamma$. Then (PC) adds the pair $\{x, y\}$, so $G = \gamma$ on $Z(P)$, and $G$ and one of its children are deleted by (D1).
--
--   **Formalization Note** The hypotheses are written out as `State.Reduced`, the negated case predicates, and conditions on gate `0` (the minimal AND).
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - generalization: standing assumption a > d of §4.2–§4.3 → no assumption on a; reason: the step does not use a > d; the statement with it is a special case
--   - reading: the paragraph describes an operation and its effect (complement x, y, add the pair {x, y} by (PC), delete G and one child by (D1); ∆m = 0, ∆s ≤ −2, ∆q = 1, ∆W ≤ −10) → there is a state σ′ valid for the same C₀ with these changes of m, q, s and W; reason: the proof of Lemma 4.2 uses exactly the existence of such a successor with these changes; Δa follows from Δm and Δq
--   - encoding: the state reached at the end of §4.2 with G not the output → hypotheses Reduced, ¬ Case 1–3, gate 0 AND-type with inputs the parameters x and y, output ≠ gate 0; reason: the paper's assumptions at this point, written out
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4.3, p.24, "Case 4: both inputs x, y of G are unpaired"

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

/-- **Case 4: both inputs `x, y` of the minimal AND `G` are unpaired** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4.3, p.24). After
complementing `x`, `y` if necessary, (PC) adds the pair `{x, y}`, so `G = γ` on `Z(P)`; `G` and one of
its children are deleted by (D1): "∆m = 0 …, ∆s ≤ −2 (as G and one of its children are deleted), ∆q = 1
(as the pair {x, y} is added), and ∆a = ∆m − ∆q = −1. This gives, ∆W ≤ −2 + 4 − 6 − 6 = −10." The
successor is valid for the same original circuit `C₀`.

**Formalization Note** The hypotheses are the state reached at the end of §4.2: no preliminary reduction applies
(`State.Reduced`, not Cases 1–3), the minimal AND `G` is the first gate, it is AND-type, it reads the
parameters `x` and `y`, and `G` is not the output (otherwise Lemma 2.2 applies, p.24). The paper's
standing assumption `a > d` is not used by this step and is omitted. -/
theorem case_4 {n : ℕ} (C₀ : Circuit n) (σ : State n) (hσ : σ.Valid C₀) (hred : σ.Reduced)
    (h1 : ¬ σ.Case1Applicable) (h2 : ¬ σ.Case2Applicable) (h3 : ¬ σ.Case3Applicable)
    (h : 0 < σ.circ.size) (hand : IsAndOp (σ.circ.op ⟨0, h⟩)) (x y : Fin σ.m)
    (hx : σ.circ.in₁ ⟨0, h⟩ = .input (.inl x)) (hy : σ.circ.in₂ ⟨0, h⟩ = .input (.inl y))
    (hGout : σ.circ.out ≠ .gate ⟨0, h⟩)
    (hxu : ¬ σ.IsPaired x) (hyu : ¬ σ.IsPaired y) :
    ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.m = σ.m ∧ σ'.q = σ.q + 1 ∧ σ'.s + 2 ≤ σ.s ∧
      σ'.W + 10 ≤ σ.W := by sorry

end AffDisp4n
