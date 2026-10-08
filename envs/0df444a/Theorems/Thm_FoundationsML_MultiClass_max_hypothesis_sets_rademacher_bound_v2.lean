-- Prove2me | Theorems.Thm_FoundationsML_MultiClass_max_hypothesis_sets_rademacher_bound_v2
-- name    : FoundationsML.MultiClass.max_hypothesis_sets_rademacher_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:08.484252+00:00
-- url     : https://prove2.me/theorems/45fa9688-7cc4-41bf-82d4-a54a1d9991f2
-- title:
--   Lemma 9.1 — Rademacher complexity of a max-of-hypothesis-sets family (bounded families)
-- statement:
--   **Statement (Lemma 9.1, p. 216, PDF p. 233).** Let $F_1,\dots,F_l$ be $l\ge1$ hypothesis sets in $\mathbb R^X$, each mapping into a bounded interval $[a,b]$ (Definition 3.1's standing assumption), and $G=\{\max\{h_1,\dots,h_l\}:h_i\in F_i\}$. Then, for any sample $S$ of size $m$, $\hat R_S(G)\le\sum_{j=1}^l\hat R_S(F_j)$.
--
--   **Formalization Note.** The retired version used the retired `EmpiricalRademacherComplexity`, whose `⨆ g ∈ G, …` on $\mathbb R$ is clipped at $0$ and returns the junk value $0$ for an unbounded family, so an unbounded cone $F_1$ had complexity $0$ while the bounded max-family did not (the accepted disproof). The corrected `EmpiricalRademacherComplexity` (`_v2`, supremum over exactly the family) is used and Definition 3.1's boundedness of each $F_j$ is explicit; for an unbounded $F_j$ the book's right-hand side is $+\infty$. The index set `ι` with `[Fintype ι] [Nonempty ι]` is $[l]$, $l\ge1$; `MaxFamily F` is the pointwise maximum family. Edge cases: an empty $F_j$ makes $G$ empty and both sides $\ge0$ with the left side $0$; $m=0$ gives $0\le0$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 216, Lemma 9.1 (PDF p. 233)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_EmpiricalRademacherComplexity_v2
import Definitions.Def_FoundationsML_MultiClass_MaxFamily

namespace FoundationsML.MultiClass

/-- Lemma 9.1 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 216, PDF p. 233). Let `F_1,…,F_l` be `l ≥ 1` hypothesis sets in `ℝ^X`
(bounded, as Definition 3.1 requires) and `G = {max{h_1,…,h_l} : h_i ∈ F_i}`. Then, for any
sample `S` of size `m`, the empirical Rademacher complexity of `G` is bounded by
`∑_{j=1}^l R̂_S(F_j)`.

**Formalization Note.** Replaces `max_hypothesis_sets_rademacher_bound`, which used the
retired `EmpiricalRademacherComplexity` whose supremum `⨆ g ∈ G, …` on `ℝ` is clipped at `0`
and returns the junk value `0` for an unbounded family, so an unbounded `F_j` had complexity
`0` while `G` did not (the disproof). The corrected `EmpiricalRademacherComplexity` (`_v2`,
supremum over exactly the family) is used, and Definition 3.1's standing assumption that each
family maps into a bounded interval `[a,b]` is explicit (`hFb`); for an unbounded `F_j` the
book's right-hand side would be `+∞`. The index set `ι` with `[Fintype ι] [Nonempty ι]` is
the book's `[l]`, `l ≥ 1`. -/
theorem max_hypothesis_sets_rademacher_bound_v2
    {X ι : Type*} [Fintype ι] [Nonempty ι] (F : ι → Set (X → ℝ))
    (hFb : ∃ a b : ℝ, ∀ j, ∀ g ∈ F j, ∀ x, g x ∈ Set.Icc a b)
    (m : ℕ) (S : Fin m → X) :
    EmpiricalRademacherComplexity (MaxFamily F) S ≤
      ∑ j, EmpiricalRademacherComplexity (F j) S := by sorry

end FoundationsML.MultiClass
