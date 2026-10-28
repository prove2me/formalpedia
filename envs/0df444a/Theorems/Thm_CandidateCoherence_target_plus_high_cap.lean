-- Prove2me | Theorems.Thm_CandidateCoherence_target_plus_high_cap
-- name    : CandidateCoherence.target_plus_high_cap
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:39:35.44276+00:00
-- url     : https://prove2.me/theorems/e844bf7f-c8e2-4e79-99ff-864c08c90dd6
-- title:
--   An ordinary exclusion bounds targets together with high vertices
-- statement:
--   Fix a directed relation \(R\), binary labels \(\ell\), a child predicate \(P\), and two children at every vertex. Let \(T,H\) be disjoint finite sets. Each vertex of \(T\) has a designated color whose other child satisfies \(P\); both children of every vertex of \(H\) satisfy \(P\). Assume each vertex in \(T\cup H\) has at most \(q\) failed guards. If no ordinarily coherent \(a\)-vertex configuration of tolerance \(q\) exists, then
--   \[
--   |T|+|H|<a.
--   \]
--   This strengthens a target-prefix cap by including high vertices at the same failure budget.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, CandidateCoherence, lines 156–180; source SHA256 c389062dc583cd307e3b5ebc46a8b3f3386215560a89a02cd6a0b7f6300c678f.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace MinmaxLocal
end MinmaxLocal
namespace TournamentHighRows
end TournamentHighRows
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CandidateCoherence
end CandidateCoherence
open CandidateCoherence
open scoped Classical
open MinmaxLocal TournamentHighRows
variable {N : ℕ} {V X : Type}
variable [Fintype V]

theorem CandidateCoherence.target_plus_high_cap (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X)
    (T H : Finset V) (hdisjoint : Disjoint T H) (q a : ℕ)
    (hexcl : NoOrdinary R ell q a) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ b : Bool, b ≠ color w → P (children w b))
    (hhigh : ∀ w ∈ H, ∀ b : Bool, P (children w b))
    (hbudgetT : ∀ v ∈ T, (guardFailures R ell P children v).card ≤ q)
    (hbudgetH : ∀ v ∈ H, (guardFailures R ell P children v).card ≤ q) :
    T.card + H.card < a := by sorry
