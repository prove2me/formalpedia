-- Prove2me | Theorems.Thm_DirTeleMC_jumpgreedy_length
-- name    : DirTeleMC.jumpgreedy_length
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:36:44.50831+00:00
-- url     : https://prove2.me/theorems/92f17fdc-e0e3-48ca-8005-b854c72acf93
-- title:
--   Proof of Theorem 1.1, p.31 — every run of JUMPGREEDY returns a schedule of length $O(\ell^3\log k)(\mathrm{OPT}+k^{1/\ell})$
-- statement:
--   There is an absolute constant $C$ such that for every integer $\ell \ge 2$ and every well-formed instance $(G, s, K, k)$ (DTM is the case $k = |K|$), JUMPGREEDY with parameter $\ell$ has a run, and every schedule $S$ it can return is valid, informs $k$ terminals, and satisfies
--   $$|S| \le C\,\ell^3 \ln k\,\left(T' + k^{1/\ell}\right)$$
--   for every valid schedule of length $T'$ that informs $k$ terminals.
--
--   This is the length half of Theorem 1.1, proved on p.31 from Lemmas B.2, B.3, B.6 and the comparison jump arborescence.
--
--   Differences from the source:
--   - encoding: O(ℓ³ log k)(OPT + k^{1/ℓ}) → one absolute real C fixed before ℓ and the instance; natural logarithm; real power k^{1/ℓ}; reason: the meaning of the O-notation with constants independent of ℓ and the instance
--   - encoding: OPT, the minimum number of rounds → every valid schedule S′ informing k terminals; reason: the same claim without a minimum over a possibly empty set
--   - generalization: the deterministic algorithm JUMPGREEDY → every run of the relation JumpGreedyRun (all ties open); reason: every deterministic tie-breaking is one of the runs
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), proof of Theorem 1.1, "The case OPT ≥ k" and "The loads of J and the schedule", p.31 (PDF p.32)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_JumpGreedyRun

namespace DirTeleMC

/-- **The length half of the proof of Theorem 1.1.**
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), proof of Theorem 1.1, p.31: "The case OPT ≥ k. The schedule of line 2 has length at most 2OPT by Lemma B.3,
and the returned schedule is not longer." … "The loads of J and the schedule. By Lemma B.6 with J′ = J* and
ν = k², the top call returns a structure J that covers k terminals (all terminals for DTM, so J is then a jump
arborescence of depth η), and every load of J is at most Γ(2 ln k + (1 + ln k)/4) ≤ 3Γ ln k, as k ≥ 2. Since
Γ ≤ µ + 1 = 20(2ℓ − 1)ℓ(OPT + ρ + 1) + 1, ρ < k^{1/ℓ} + 1 and OPT ≥ 1, this gives
Λ(J) = O(ℓ² log k)(OPT + k^{1/ℓ}). By Lemma B.2 and (2), with ηθ = (2ℓ − 1)OPT, SCHEDULE(J) informs k terminals
within ℓ max{Λ(J), k^{1/ℓ}, 2} + (2ℓ − 1)OPT = O(ℓ³ log k)(OPT + k^{1/ℓ}) rounds. Line 8 keeps the shortest
schedule found, so the returned schedule is not longer."

There is an absolute constant `C` such that for every `ℓ ≥ 2` and every well-formed instance (DTM is `k = |K|`),
JUMPGREEDY with parameter `ℓ` has a run, and every run returns a valid schedule that informs `k` terminals and
whose length is at most `C ℓ³ ln k (T′ + k^{1/ℓ})` for every valid schedule of length `T′` informing `k`
terminals.

**Formalization Note.** `C` is fixed before `ℓ` and the instance. OPT is written as "every valid `S′`", so no
minimum over a possibly empty set is taken. `Real.log` is natural, `k^{1/ℓ}` the real power. -/
theorem jumpgreedy_length :
    ∃ C : ℝ, ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ I : Inst, I.WF →
      (∃ S, JumpGreedyRun ℓ I S) ∧
      ∀ S, JumpGreedyRun ℓ I S → S.Valid I ∧ S.InformsK I ∧
        ∀ S' : Schedule I.n, S'.Valid I → S'.InformsK I →
          (S.length : ℝ) ≤
            C * (ℓ : ℝ) ^ 3 * Real.log I.k * ((S'.length : ℝ) + (I.k : ℝ) ^ ((1 : ℝ) / ℓ)) := by sorry

end DirTeleMC
