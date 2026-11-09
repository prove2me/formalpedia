-- Prove2me | Theorems.Thm_ElimAgree_theorem_3_8_zero_bits
-- name    : ElimAgree.theorem_3_8_zero_bits
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:31:25.214327+00:00
-- url     : https://prove2.me/theorems/418aafc2-02c5-470f-9709-eb479f71221e
-- title:
--   Proof of Theorem 3.8 — zero communication errs with probability $\ge2^{-k}$
-- statement:
--   Let $n\ge1$ and $k\ge1$, and consider a common-output protocol for $\mathrm{Elim}(\mathrm{DISJ}_n^k)$ that sends no bits. Let Alice hold $[n]$ in every instance. Then Bob has an input, each of whose sets is empty or a singleton, on which the protocol fails with probability at least $2^{-k}$.
--
--   Consequently every protocol with error below $2^{-k}$ communicates at least one bit.
--
--   Differences from the source:
--   - generalization: n ≥ 3 (Theorem 3.8's range) → n ≥ 1; reason: the argument needs only one element of [n]; it specializes to n ≥ 3
--   - encoding: no bits are sent → every tree in the support has depth 0 (CostLE μ 0); reason: Lean convention; same protocols
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), proof of Theorem 3.8, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ElimAgree_disjAns

namespace ElimAgree

/-- Zero communication errs with probability at least `2^{−k}` (proof of Theorem 3.8, p.11),
Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission): for `n ≥ 1` and `k ≥ 1`, if a common-output protocol for `Elim(DISJ_n^k)` sends no bits,
then with Alice holding `[n]` in every instance there is an input of Bob, each of whose sets is
empty or a singleton, on which the failure probability is at least `2^{−k}`.

**Formalization Note.** "No bits are sent" is `CostLE μ 0`: every tree in the support is a leaf.
The paper's range is `n ≥ 3`; the argument needs only `n ≥ 1`. -/
theorem theorem_3_8_zero_bits (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (μ : PMF (ComProt n k))
    (hμ : CostLE μ 0) :
    ∃ Y : Inp n k, (∀ i, (Y i).card ≤ 1) ∧
      ENNReal.ofReal ((1 / 2) ^ k) ≤ comErr disjAns μ (fun _ => Finset.univ) Y := by sorry

end ElimAgree
