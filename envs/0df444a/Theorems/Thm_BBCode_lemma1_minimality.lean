-- Prove2me | Theorems.Thm_BBCode_lemma1_minimality
-- name    : BBCode.lemma1_minimality
-- status  : Proved
-- author  : @Winningatmath
-- created : 2026-10-16T17:57:42.369678+00:00
-- url     : https://prove2.me/theorems/12d80f98-e4b8-4888-80a3-fc864a057dc6
-- title:
--   Lemma 1 — minimality: no proper even subset of a minimum-weight logical
-- statement:
--   Let $\mathcal C$ (checks) and $\mathcal O$ (observables) be finite families of finite subsets of a set $\alpha$. Call a finite $S\subseteq\alpha$ a **logical** if $|S\cap c|$ is even for every $c\in\mathcal C$ and $|S\cap o|$ is odd for some $o\in\mathcal O$. If $z$ is a logical of minimum cardinality among all finite logicals, then for every nonempty $T\subsetneq z$,
--   $$\neg\big(\forall c\in\mathcal C,\ |T\cap c|\ \text{is even}\big).$$
--
--   This lemma justifies the 'kernel' prune of the source's exhaustive distance search: a partial support that already contains a nonempty set even on every check cannot extend to a minimum-weight logical.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits: an exhaustive classification and checkable distances to 360 qubits, Zenodo v1.0.0 (2026), https://doi.org/10.5281/zenodo.23382175, §4, Lemma 1 (p. 3)

import Mathlib
import Definitions.Def_BBCode_Setting

namespace BBCode

theorem lemma1_minimality {α : Type*} [DecidableEq α]
    (checks obs : Finset (Finset α)) (z : Finset α)
    (hz : (∀ c ∈ checks, Even (z ∩ c).card) ∧ ∃ o ∈ obs, Odd (z ∩ o).card)
    (hmin : ∀ S : Finset α, ((∀ c ∈ checks, Even (S ∩ c).card) ∧
      ∃ o ∈ obs, Odd (S ∩ o).card) → z.card ≤ S.card)
    (T : Finset α) (hT : T ⊂ z) (hne : T.Nonempty) :
    ¬ ∀ c ∈ checks, Even (T ∩ c).card := by sorry

end BBCode
