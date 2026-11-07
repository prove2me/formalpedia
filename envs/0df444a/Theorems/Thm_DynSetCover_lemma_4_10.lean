-- Prove2me | Theorems.Thm_DynSetCover_lemma_4_10
-- name    : DynSetCover.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:32.52816+00:00
-- url     : https://prove2.me/theorems/3fc7885f-50ef-4864-a4a1-208a7693bff6
-- title:
--   Lemma 4.10 — $\sum_{j\in\mathbb Z}2^{j-1}g_j(A)\le(1+\ln\Delta)\,\mathrm{OPT}(A)$
-- statement:
--   Let $A$ be a nonempty set of elements and $\Delta=\max_{S\in\mathcal F}|S\cap A|$. The augmented optima satisfy
--   $$\sum_{j\in\mathbb Z}2^{j-1}g_j(A)\le(1+\ln\Delta)\,\mathrm{OPT}(A).$$
--
--   Combined with a scale-by-scale bound $N_i\le K\,g_i(A_t)$, this turns the retained-cost bounds into an $O(1+\log\Delta_t)$ approximation ratio.
--
--   **Formalization Note** The series over $\mathbb Z$ is stated through its finite partial sums: the bound holds for every finite set $J$ of integers. All terms are nonnegative, so this is the same as summability together with the bound.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - generalization: an update boundary with $A=A_t\neq\emptyset$ → every nonempty finite set $A$ of elements; reason: the statement mentions only the instance and $A$
--   - encoding: $\sum_{j\in\mathbb Z}$ → every finite partial sum $\sum_{j\in J}$; reason: the terms are nonnegative, so the bound on all finite partial sums is the bound on the series and implies its convergence
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Lemma 4.10, p.37 (PDF 39)

import Mathlib
import Definitions.Def_DynSetCover_Rounding

namespace DynSetCover

/-- **Lemma 4.10** (Paul, Solomon, STOC 2027 submission, sha256 a671756b…, p.37 (PDF 39)).
For a nonempty set `A` of elements with `Δ = max_{S∈F} |S ∩ A|`,
`Σ_{j∈ℤ} 2^{j−1} g_j(A) ≤ (1 + ln Δ) OPT(A)`.

**Formalization Note.** The sum over all integers is stated through its finite partial sums:
the bound holds for every finite set `J ⊆ ℤ`. Since every term is nonnegative (Lemma 4.2), this
is equivalent to summability together with the bound on the sum, and it avoids the junk value
`0` of a non-summable `tsum`. The paper fixes `A = A_t` at an update boundary; the statement
mentions only the instance and `A`, so it is stated for every nonempty `A`. -/
theorem lemma_4_10 (inst : Instance) (A : Finset (Fin inst.u)) (hA : A.Nonempty)
    (J : Finset ℤ) :
    ∑ j ∈ J, (2 : ℝ) ^ (j - 1) * inst.g j A ≤
      (1 + Real.log (inst.maxLoad A : ℝ)) * inst.OPT A := by sorry

end DynSetCover
