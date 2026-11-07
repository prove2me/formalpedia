-- Prove2me | Theorems.Thm_DataValidation_lemma_9
-- name    : DataValidation.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:22.931789+00:00
-- url     : https://prove2.me/theorems/259f1bb5-7673-416c-b3a5-61482d8c70d4
-- title:
--   Lemma 9 — obtainability is a path condition
-- statement:
--   Let $E$ be an acyclic edge set and $R\subseteq E$. Then $R$ is obtainable if and only if
--
--   $$\text{for every edge }(u,v)\in R,\ \text{there is no directed }u\text{-}v\text{ path in }E\setminus R.$$
--
--   This turns the existence of a removal order into a static criterion on the set $R$ itself.
--
--   Differences from the source: none.
-- source:
--   Tinguely, van der Heijden, Approximation and Hardness for the Data Validation Problem, arXiv:2611.06773 (sha256 6595f819…), Lemma 9, p.6

import Definitions.Def_DataValidation_Obtainable

set_option autoImplicit false

namespace DataValidation

/-- **Lemma 9** of arXiv:2611.06773 (sha256 6595f819…), p.6: for any acyclic edge set `E` and any
`R ⊆ E`, `R` is obtainable iff for every edge `(u, v) ∈ R` there is no `u`-`v` path in `E ∖ R`. -/
theorem lemma_9 {V : Type*} [DecidableEq V] (E R : Finset (V × V)) (hE : IsAcyclic E)
    (hR : R ⊆ E) : Obtainable E R ↔ ∀ e ∈ R, ¬ HasPath (E \ R) e.1 e.2 := by sorry

end DataValidation
