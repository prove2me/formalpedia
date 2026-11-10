-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_7_2
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:31:58.935698+00:00
-- url     : https://prove2.me/theorems/535dc022-8afe-4108-b302-2669c61d7cb8
-- title:
--   Lemma 7.2 — accepted-trial distribution
-- statement:
--   Fix $0\le\alpha<1/2$, $s=2\lceil 4/(1-2\alpha)^2\rceil$ and $n\ge\lceil 4s/(1-2\alpha)\rceil$. Take one trial of Protocol 3, together with an independent uniform permutation $\rho$ giving the order of the nonparticipant rows. Conditional on acceptance, the pair (table, labeling) has the following law: the table has the explicit law `p3AcceptedTableLaw`, and independently the labeling is a uniform bijection. In that law the sorted participant tags form a uniform $s$-subset; the unmatched position is uniform; the other participants get statuses $1..s-1$ by a uniform bijection; the unmatched row has flag 1; nonparticipant rows have status and flag 0; requested rows have independent Bernoulli$(1/(n-s+1))$ flags; and all bits and all nonparticipant tags are independent and uniform. The acceptance probability is at least $1/(2e)$.
--
--   Differences from the source:
--   - encoding: server labels [n] = {1,…,n}; positions and tags counted from 1 → `Fin n` = {0,…,n−1}; positions and tags counted from 0; reason: relabelling by −1 changes no instance
--   - reading: put the nonparticipant rows afterward in an independent uniform order → nonparticipants ordered by an independent uniform permutation ρ of the labels; reason: this is an independent uniform order
--   - encoding: conditional on the table, the server labels are assigned by a uniform bijection → the joint law of (table, labeling) is the table law times an independent uniform permutation; reason: the same statement as a product law
--   - encoding: standing parameters of Section 7.1 → hypotheses 0 ≤ α < 1/2 and n ≥ ⌈4s/(1−2α)⌉ with s = s3 α; reason: Section 7.1’s standing assumptions
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 7.2, p. 33-34 (PDF 35-36)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol3

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 7.2 (accepted-trial distribution). -/
theorem lemma_7_2 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1 / 2) (n : ℕ)
    (hn : ⌈4 * (s3 α : ℝ) / (1 - 2 * α)⌉₊ ≤ n) :
    (pcond ((p3TrialRaw n (s3 α)).bind fun x =>
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map fun ρ => (x, ρ))
        (fun y => p3Accept (s3 α) y.1)).map
      (fun y => (p3Table y.1 y.2, p3Labeling y.1 y.2)) =
      (p3AcceptedTableLaw n (s3 α)).bind (fun tb =>
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map fun σ : Equiv.Perm (Fin n) => (tb, (σ : Fin n → Fin n))) ∧
    1 / (2 * Real.exp 1) ≤ probE (p3TrialRaw n (s3 α)) (p3Accept (s3 α)) := by sorry

end ChoiSemiHonestMPC.OTUpper
