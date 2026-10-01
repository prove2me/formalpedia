-- Prove2me | Theorems.Thm_FoundationsML_MultiClass_max_hypothesis_sets_rademacher_bound
-- name    : FoundationsML.MultiClass.max_hypothesis_sets_rademacher_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:32:46.457823+00:00
-- url     : https://prove2.me/theorems/f69c7659-cc88-4f8d-bb58-32acb0f8ca63
-- title:
--   Lemma 9.1 — Rademacher complexity of a max-of-hypothesis-sets family
-- statement:
--   **Statement (Lemma 9.1, p. 216, PDF p. 233).** Let $F_1,\dots,F_l$ be $l\ge1$ hypothesis
--   sets in $\mathbb R^X$ and $G=\{\max\{h_1,\dots,h_l\}:h_i\in F_i\}$. Then, for any sample $S$
--   of size $m$, $\hat R_S(G) \le \sum_{j=1}^l \hat R_S(F_j)$. Used twice in Theorem 9.2's
--   proof: once directly, and once (via a $k$-way max over classes) to produce the $4k$ factor.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 216, Lemma 9.1 (PDF p. 233)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_EmpiricalRademacherComplexity
import Definitions.Def_FoundationsML_MultiClass_MaxFamily

namespace FoundationsML.MultiClass

/-- Lemma 9.1 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 216, PDF p. 233). Let `F_1,…,F_l` be `l ≥ 1` hypothesis sets in `ℝ^X` and
`G = {max{h_1,…,h_l} : h_i ∈ F_i}`. Then, for any sample `S` of size `m`, the empirical
Rademacher complexity of `G` is bounded by `∑_{j=1}^l R̂_S(F_j)`. -/
theorem max_hypothesis_sets_rademacher_bound
    {X ι : Type*} [Fintype ι] [Nonempty ι] (F : ι → Set (X → ℝ)) (m : ℕ) (S : Fin m → X) :
    EmpiricalRademacherComplexity (MaxFamily F) S ≤
      ∑ j, EmpiricalRademacherComplexity (F j) S := by sorry

end FoundationsML.MultiClass
