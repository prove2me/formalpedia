-- Prove2me | Theorems.Thm_ConvexRMDP_lemma_4_2
-- name    : ConvexRMDP.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:42.434834+00:00
-- url     : https://prove2.me/theorems/f7eaa0a3-6e7b-4569-b91f-fc5f8bfd81e3
-- title:
--   Lemma 4.2: $x \mapsto \tilde t(x)_s$ is concave on $(\mathbb R^*_+)^S$
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP and $b > 0$. For each $s \in \mathcal S$ the function
--   $$
--   x \mapsto \tilde t(x)_s = \sum_{a \in \mathcal A} \omega_b(s,a) \min_{p \in \mathcal U_{sa}} \prod_{s' \in \mathcal S} x_{s'}^{\gamma p_{s'}}
--   $$
--   defined in (4.5) is concave on $(\mathbb R^*_+)^{\mathcal S}$, the set of vectors with positive entries.
--
--   Concavity of $\tilde t$ is what makes the set $\{x \le \tilde t(x)\}$, and hence the feasible set of the program (4.7), convex.
--
--   Differences from the source:
--   - generalization: min over p ∈ 𝒰_sa (the paper's min presupposes attainment) → infimum (sInf) over an arbitrary nonempty 𝒰_sa ⊆ Δ(S); reason: the set is nonempty and bounded below; whenever the minimum is attained the infimum equals it, so the statement specializes to the source's.
--   - reading: 𝒰_sa ⊆ Δ(S) with min_{p ∈ 𝒰_sa} → 𝒰_sa nonempty (field U_nonempty of RMDP); reason: a minimum over an empty set is undefined; the paper's formulas presuppose nonemptiness.
--   - encoding: (ℝ*₊)^S → Set.pi univ (fun _ => Ioi 0); reason: the set of vectors with positive entries; same set.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), Lemma 4.2, p.13

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_tOp

namespace ConvexRMDP

/-- **Lemma 4.2** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.13): for each `s ∈ S`, the function
`x ↦ t̃(x)_s` of (4.5) is concave on `(ℝ*₊)^S`.

**Formalization Note.** `(ℝ*₊)^S` is `Set.pi Set.univ (fun _ => Set.Ioi 0)`, the vectors with
positive entries; concavity is not claimed outside it (where `Real.rpow` is not the paper's power).
`b > 0` is the regularization scalar of §4.2. -/
theorem lemma_4_2 {S A : Type*} [Fintype S] [Fintype A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) (s : S) :
    ConcaveOn ℝ (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) (fun x => M.tOp b x s) := by sorry

end ConvexRMDP
