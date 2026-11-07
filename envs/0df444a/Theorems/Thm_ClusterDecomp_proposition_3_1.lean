-- Prove2me | Theorems.Thm_ClusterDecomp_proposition_3_1
-- name    : ClusterDecomp.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:30.765185+00:00
-- url     : https://prove2.me/theorems/82d690bc-5359-411e-b1e7-e7a2873d297b
-- title:
--   Proposition 3.1, p.9 — every $\alpha$-fair cut is an $\alpha$-approximate minimum cut
-- statement:
--   Let $c$ be capacities on a finite vertex set and $(S,T)$ an $\alpha$-fair $s,t$-cut, $\alpha>0$. Then $(S,T)$ is an $s,t$-cut, and for every $s,t$-cut $(S',T')$,
--   $$c(S,T)\le\alpha\,c(S',T').$$
--
--   This is how fairness gives the capacity bound (3) in Lemma 3.2.
--
--   Differences from the source:
--   - generalization: an undirected capacitated graph with α ≥ 1 implied → any capacity function, not assumed symmetric, and any α > 0; reason: the inequality uses neither; undirected graphs and α ≥ 1 are instances
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Proposition 3.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_ClusterDecomp_IsFairCut

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Proposition 3.1.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), Proposition 3.1, p.9 (PDF p.11).

"Every α-fair s, t-cut is an α-approximation to the minimum s, t-cut."

An `α`-fair cut `S` is an `s,t`-cut, and its capacity is at most `α` times that of any `s,t`-cut `S′`.

**Formalization Note.** `0 < α` suffices, and no symmetry of `c` is used. -/
theorem proposition_3_1 {W : Type*} [Fintype W] [DecidableEq W] (c : W → W → ℝ) (s t : W)
    (S : Finset W) (α : ℝ) (hα : 0 < α) (hS : IsFairCut c s t S α) :
    s ∈ S ∧ t ∉ S ∧ ∀ S' : Finset W, s ∈ S' → t ∉ S' → cutCap c S Sᶜ ≤ α * cutCap c S' S'ᶜ := by sorry

end ClusterDecomp
