-- Prove2me | Theorems.Thm_DirTeleMC_Supplement_theorem_1_4
-- name    : DirTeleMC.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:45:20.062743+00:00
-- url     : https://prove2.me/theorems/fe5114ab-031a-47c2-9dc6-d15f7c5ce950
-- title:
--   Theorem 1.4 — distinguishing acyclic DTM instances with $\mathrm{OPT}\le C_\epsilon\log_2k$ from those with $\mathrm{OPT}\ge(1-\epsilon)\ln k\cdot C_\epsilon\log_2k$ is NP-hard
-- statement:
--   For every $\epsilon\in(0,1)$ there is a constant $C_\epsilon>0$ such that it is NP-hard to distinguish acyclic DTM instances with
--   $$\mathrm{OPT}\le C_\epsilon\log_2k$$
--   from acyclic DTM instances with
--   $$\mathrm{OPT}\ge(1-\epsilon)\ln k\cdot C_\epsilon\log_2k,$$
--   where $k=|K|$ is the number of terminals. NP-hardness of the distinction means: for every language $L$ in NP over a finite nonempty alphabet there is a polynomial-time computable map from strings to (encoded) instances that sends every string of $L$ to an instance of the first kind and every other string to an instance of the second kind that is not of the first kind (a promise problem has disjoint YES and NO sets).
--
--   So the logarithmic hardness of directed telephone multicast persists even when the optimum is of order $\log k$, its least possible order.
--
--   **Formalization Note** Gap NP-hardness is the published `SetCoverThreshold.SetCover.GapNPHard`, built on Cook's one-tape machines and `NP` (`CookPvsNP_defs`), with instances encoded by the published `encInst`. $\log_2$ and $\ln$ are real logarithms.
--
--   Differences from the source:
--   - encoding: it is NP-hard to distinguish the two kinds of instances → SetCoverThreshold.SetCover.GapNPHard encInst Yes No: every NP language over every finite nonempty alphabet maps in polynomial time (Cook's machines) to encoded instances, members to Yes and non-members to No; reason: the standard Karp reading of gap NP-hardness; the paper names no machine model
--   - reading: a constant Cϵ → a real Cϵ > 0; reason: the constant of the proof, λ + 2C + 3, is positive; the conclusion only becomes stronger
--   - generalization: acyclic DTM instances (k terminals, all reachable, s ∉ K) → acyclic DTM instances that are moreover well formed with k ≥ 2 (Inst.WF, k = |K|); reason: restricting both the YES and the NO instances makes the hardness claim stronger; the paper's reduction has k = m ≥ 2 terminals
--   - encoding: OPT ≤ Cϵ log₂ k; OPT ≥ (1 − ϵ) ln k · Cϵ log₂ k → some valid schedule informing all terminals has length ≤ C log₂ k; every valid schedule informing all terminals has length ≥ (1 − ϵ) ln k · C log₂ k; reason: OPT as a comparison with valid schedules; same instances
--   - reading: NO instances, those with OPT ≥ (1 − ϵ) ln k · Cϵ log₂ k → NO instances, those with OPT ≥ (1 − ϵ) ln k · Cϵ log₂ k that are not YES instances; reason: distinguishing presupposes disjoint YES and NO sets (a promise problem); for small k, (1 − ϵ) ln k < 1 and the two bounds overlap, so the literal sets would let a constant map to one instance in both sets (k = 2, arcs s→a, s→b, OPT = 2, C = 2) satisfy the statement; the paper's NO instances (large k) are not YES instances, so the reading is the paper's
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Theorem 1.4, p.4 (PDF p.5); restated p.51 (PDF p.52); proof pp.51–52 (PDF pp.52–53)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_encInst
import Definitions.Def_DirTeleMC_Supplement_AcyclicDTM
import Definitions.Def_SetCoverThreshold_SetCover_Complexity

namespace DirTeleMC.Supplement

open DirTeleMC

/-- **Theorem 1.4** (logarithmic hardness with `OPT = O(log k)`).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Theorem 1.4, p.4 (restated p.51, proof pp.51–52): "For every ϵ ∈ (0, 1) there is a
constant Cϵ such that it is NP-hard to distinguish acyclic DTM instances with OPT ≤ Cϵ log₂ k from those with
OPT ≥ (1 − ϵ) ln k · Cϵ log₂ k."

For every `ϵ ∈ (0, 1)` there is a real `C > 0` such that the promise problem with YES instances the acyclic DTM
instances having a valid schedule of length at most `C log₂ k` that informs all terminals, and NO instances the acyclic
DTM instances on which every valid schedule informing all terminals has length at least `(1 − ϵ) ln k · C log₂ k`
and which are not YES instances, is
NP-hard: every NP language over every finite nonempty alphabet maps, by a polynomial-time computable function, to
encoded instances so that members go to YES instances and non-members to NO instances.

**Formalization Note.** Gap NP-hardness is the published `SetCoverThreshold.SetCover.GapNPHard` (Cook's one-tape
machines and `NP` of `CookPvsNP_defs`), with instances encoded by the published `encInst`. OPT is written through
valid schedules informing all `k = |K|` terminals. `Real.logb 2` is `log₂`, `Real.log` is `ln`. A promise problem
has disjoint YES and NO sets, so the NO instances are also required not to be YES instances; for small `k` the two
bounds overlap (`(1 − ϵ) ln k < 1`), and without this a constant map to one instance in both sets would satisfy the
statement. -/
theorem theorem_1_4 :
    ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 → ∃ C : ℝ, 0 < C ∧
      SetCoverThreshold.SetCover.GapNPHard encInst
        (fun I => AcyclicDTM I ∧ ∃ S : Schedule I.n, S.Valid I ∧ S.InformsK I ∧
          (S.length : ℝ) ≤ C * Real.logb 2 I.k)
        (fun I => AcyclicDTM I ∧ (∀ S : Schedule I.n, S.Valid I → S.InformsK I →
          (1 - ϵ) * Real.log I.k * (C * Real.logb 2 I.k) ≤ (S.length : ℝ)) ∧
          ¬ ∃ S : Schedule I.n, S.Valid I ∧ S.InformsK I ∧
            (S.length : ℝ) ≤ C * Real.logb 2 I.k) := by sorry

end DirTeleMC.Supplement
