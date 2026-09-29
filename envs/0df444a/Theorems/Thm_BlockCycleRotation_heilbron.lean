-- Prove2me | Theorems.Thm_BlockCycleRotation_heilbron
-- name    : BlockCycleRotation.heilbron
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:30.833684+00:00
-- url     : https://prove2.me/theorems/a73afd5d-cf23-488a-93ff-f66692a0c82b
-- title:
--   Equation (eq. heilbron): from move counts to lattice point counts
-- statement:
--   For $n>0$,
--   $$\sum_{k \in \mathrm{Sh}(n)} \operatorname{remSum}(n,k) = \sum_{k \in \mathrm{Sh}(n)} \gcd(n,k) \;+\; \sum_{q \in \mathcal{Q}(n)} b(q),$$
--   where $\mathrm{Sh}(n)$ is the set of shifts the algorithm recurses on and $\mathcal{Q}(n)$ is the set of quadruples $(a,a',b,b')$ with $\gcd(a,a')=1$ arising from Heilbronn's correspondence.
--
--   This is the paper's labelled identity in §4 and the hinge of the whole average-case analysis: the left side is what the algorithm costs, the right side is a lattice-point count that analytic methods can estimate. Everything after it — the triple sum, Lemmas 16, 18 and 19 — is the evaluation of the second term on the right.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L1125-L1138

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.heilbron {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, remSum n k
      = (∑ k ∈ allShifts n, Nat.gcd n k) + ∑ q ∈ quadruplesAll n, q.2.1 := by sorry
