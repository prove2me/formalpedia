-- Prove2me | Theorems.Thm_AffDisp4n_restructure_minimal_and
-- name    : AffDisp4n.restructure_minimal_and
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:03:51.75445+00:00
-- url     : https://prove2.me/theorems/eed32695-6727-43ba-83d9-50c787d855e9
-- title:
--   §4.2 — restructuring the minimal AND: after at most two exchanges (AR), both inputs are parameters
-- statement:
--   Let $\sigma$ be a state valid for the original circuit $C_0$ to which no preliminary reduction applies: the output check has failed, no deletion (D1)–(D4) or move of an affine gate applies, and none of Cases 1–3 applies. Then there is a state $\sigma'$, valid for the same $C_0$, with
--   $$
--   m' = m, \quad s' = s, \quad q' = q, \quad W' \le W,
--   $$
--   such that either one of Cases 1–3 applies to $\sigma'$, or $\sigma'$ is reduced and its first gate $G$ (the **minimal AND**) is an AND-type gate whose two inputs are distinct parameters $x \ne y$.
--
--   In the paper, each auxiliary input of $G$ is exchanged by (AR) with an unpaired parameter it depends on, and affine gates are moved into the affine system again. Cases 4 and 5 then eliminate $G$.
--
--   **Formalization Note** `State.Reduced` says that no deletion or move applies, and `¬ OutputSimple` that the output check has failed. For parameter inputs, "independent linear parts" means two distinct parameters.
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - generalization: standing assumption a > d of §4.2–§4.3 → no assumption on a; reason: the step does not use a > d; the statement with it is a special case
--   - reading: the paragraph applies (AR) to the auxiliary inputs of G and moves affine gates (∆m = ∆s = ∆q = ∆a = ∆W = 0), then either performs one of Cases 1–3 or proceeds with both inputs of G parameters → ∃ σ′ valid for C₀ with m′ = m, s′ = s, q′ = q, W′ ≤ W, and (Case 1, 2 or 3 applies to σ′) or (σ′ reduced, its first gate AND-type with two distinct parameter inputs); reason: the existence of this state is what the proof of Lemma 4.2 uses; moves of affine gates satisfy ∆W ≤ 0 (p.22)
--   - encoding: the output check has failed, the deletions and moves of §4.1 no longer apply, and the earlier cases are inapplicable (p.22) → hypotheses ¬ OutputSimple, Reduced and ¬ CaseKApplicable for the earlier cases; reason: the paper's standing assumptions at the point where the case is checked, written out
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4.2, pp.23–24, "Restructuring the minimal AND"

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

/-- **Restructuring the minimal AND** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4.2, pp.23–24). Suppose no preliminary reduction applies:
the output check fails, none of (D1)–(D4) applies, no affine gate can be moved, and none of Cases 1–3
applies. The first gate `G` of the acyclic part is then an AND-type gate whose inputs are parameters or
auxiliary variables with independent linear parts. Each auxiliary input is exchanged by (AR) with an
unpaired parameter it depends on, with "∆m = ∆s = ∆q = ∆a = ∆W = 0", and affine gates are moved into the
affine system again, which does not increase `W`. Then either one of Cases 1–3 applies ("If one of the
Cases 1–3 applies, we perform it, and end the current iteration"), or "after at most two applications
of (AR), both inputs of G are parameters". The resulting state is valid for the same `C₀`, has the same
`m`, `s`, `q`, and has `W′ ≤ W`; in the second alternative it is reduced, and its first gate is AND-type
and reads two distinct parameters.

**Formalization Note** `State.Reduced` says that none of (D1)–(D4) applies and no affine gate can be moved into the
affine system; with `¬ OutputSimple` (the output check of §4.1 failed) these are the conditions under
which the paper checks the cases ("for each case that applies, we may assume that all earlier cases are
inapplicable", p.22). The paper's standing assumption `a > d` of §4.2 is not
used by this step and is omitted. Distinct parameters are the parameter case of "independent linear
parts". -/
theorem restructure_minimal_and {n : ℕ} (C₀ : Circuit n) (σ : State n) (hσ : σ.Valid C₀)
    (hout : ¬ σ.OutputSimple) (hred : σ.Reduced)
    (h1 : ¬ σ.Case1Applicable) (h2 : ¬ σ.Case2Applicable) (h3 : ¬ σ.Case3Applicable) :
    ∃ σ' : State n, σ'.Valid C₀ ∧ σ'.m = σ.m ∧ σ'.s = σ.s ∧ σ'.q = σ.q ∧ σ'.W ≤ σ.W ∧
      ((σ'.Case1Applicable ∨ σ'.Case2Applicable ∨ σ'.Case3Applicable) ∨
        (σ'.Reduced ∧ ∃ h : 0 < σ'.circ.size, IsAndOp (σ'.circ.op ⟨0, h⟩) ∧
          ∃ x y : Fin σ'.m, x ≠ y ∧ σ'.circ.in₁ ⟨0, h⟩ = .input (.inl x) ∧
            σ'.circ.in₂ ⟨0, h⟩ = .input (.inl y))) := by sorry

end AffDisp4n
