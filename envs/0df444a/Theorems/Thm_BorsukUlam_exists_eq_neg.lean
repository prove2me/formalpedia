-- Prove2me | Theorems.Thm_BorsukUlam_exists_eq_neg
-- name    : BorsukUlam.exists_eq_neg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T10:58:16.212417+00:00
-- url     : https://prove2.me/theorems/12581ef6-b00e-492c-b4b2-85a07a431bda
-- title:
--   Borsuk–Ulam theorem — every continuous map from the d-sphere to ℝ^d identifies some pair of antipodal points
-- statement:
--   **Statement.** For every $d \ge 0$ and every continuous map $f : S^d \to \mathbb R^d$ from the unit sphere of $\mathbb R^{d+1}$, there is a point $x \in S^d$ with $f(x) = f(-x)$.
--
--   In Lean the sphere is `Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1`, the target is `EuclideanSpace ℝ (Fin d)`, and $-x$ is the antipodal point. For $d = 0$ the target is a single point and the claim is trivial. Applied to $g(x) = f(x) - f(-x)$, the theorem gives the form for odd maps used by Lin, Wu and Zhou. In the proof of their Lemma A.2 (Appendix A.1.2, printed p. 23) they write: "The form we use says that if $d$ continuous quantities depend on a point of $S^d$, and all change sign when that point is replaced by its opposite, then some point makes all $d$ quantities zero simultaneously." They cite F. W. Simmons and F. E. Su, *Consensus-halving via theorems of Borsuk–Ulam and Tucker*, Mathematical Social Sciences 45(1) (2003) 15–25, https://doi.org/10.1016/S0165-4896(02)00087-2.
--
--   This statement generalizes `Hatcher.borsuk_ulam_sphere`, which is the case $d = 2$. It was published so that `SublinearChoresMMS.Disposal.lemma_a_2` (Lemma A.2 of Lin, Wu and Zhou, *Best-of-Many-Worlds MMS Allocation for Chores with Sublinear Disposals*) can be reduced to it. Standard proofs go through the degree of an odd map, or combinatorially through Tucker's lemma.
-- source:
--   Lin, Wu, Zhou, Best-of-Many-Worlds MMS Allocation for Chores with Sublinear Disposals (STOC 2027 submission 845), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf, p. 23, the Borsuk–Ulam theorem as used in Step 1 of the proof of Lemma A.2 (PDF p. 24), cited there as Simmons, Su, Consensus-halving via theorems of Borsuk–Ulam and Tucker, Mathematical Social Sciences 45(1) (2003) 15–25, https://doi.org/10.1016/S0165-4896(02)00087-2

import Mathlib

namespace BorsukUlam

theorem exists_eq_neg (d : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, EuclideanSpace ℝ (Fin d))) :
    ∃ x, f x = f (-x) := by
  sorry

end BorsukUlam
