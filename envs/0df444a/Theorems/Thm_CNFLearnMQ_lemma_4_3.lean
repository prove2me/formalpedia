-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_4_3
-- name    : CNFLearnMQ.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:17.701361+00:00
-- url     : https://prove2.me/theorems/c96ef6ac-4011-4cea-b3b9-a78d8c52c002
-- title:
--   Lemma 4.3 — a core lies in every clause its flip violates
-- statement:
--   Let $\Phi=(V,C)$ be a CNF formula on $n$ variables with $m=|C|\ge1$ nonempty clauses, each of width at most $k$, in which every variable occurs in at most $d$ clauses (the standing assumptions of §4, p.15).
--   Let $X$ be a solution of $\Phi$ and $R\in\mathcal R_X$ a core. Then for every clause $c\in C$ violated by $X^{\oplus R}$ (in particular the witness clause $c_R$),
--   $$R=\{v\in\mathrm{vbl}(c)\mid X_v\ne\sigma_c(v)\},$$
--   and consequently $c(X,R)\subseteq c$.
--
--   This identity is the structural fact behind every later bound: each core is the set of satisfied literals of a clause, so it determines its clause's restriction and its induced subclause is a subclause of a target clause.
--
--   Differences from the source:
--   - generalization: the witness clause $c_R$ (the first clause violated by $X^{\oplus R}$ in a fixed order) → every clause $c\in C$ violated by $X^{\oplus R}$; reason: the proof uses only that $c_R$ is violated by $X^{\oplus R}$; $c_R$ is one such clause
--   - encoding: $X_v\ne\sigma_c(v)$ and $s\subseteq c$ → `c v = some (X v)` and `Subclause`; reason: the published clause type stores the satisfying literal value, the negation of the forbidden one; same instances
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 4.3, p.16

import Mathlib
import Definitions.Def_CNFLearnMQ_cores

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 4.3, p.16 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). For a solution `X` of a CNF formula `Φ` with `m ≥ 1` nonempty
clauses of width at most `k` and maximum variable degree at most `d` (the standing assumptions of
§4, p.15), a core `R` of `X`, and a clause `c ∈ Φ` violated by `X^{⊕R}`:
`R = {v ∈ vbl(c) | X_v ≠ σ_c(v)}` and `c(X, R) ⊆ c`.

**Formalization Note** The paper states this for the witness clause `c_R` (the first violated clause
in a fixed order); the statement here holds for every clause violated by `X^{⊕R}`, which includes
`c_R`. With the published clause encoding (stored literal value = satisfying value), `X_v ≠ σ_c(v)`
reads `c v = some (X v)`, and `s ⊆ c` is `Subclause s c`. -/
theorem lemma_4_3 {n k d : ℕ} (Φ : CNF n) (hm : 1 ≤ Φ.card)
    (hw : ∀ c ∈ Φ, 1 ≤ width c ∧ width c ≤ k) (hdeg : DegreeBound Φ d)
    (X : Assignment n) (hX : X ∈ solutions Φ) (R : Finset (Fin n)) (hR : R ∈ cores Φ X)
    (c : Clause n) (hc : c ∈ Φ) (hviol : Violates c (flipOn X R)) :
    R = (support c).filter (fun v => c v = some (X v)) ∧ Subclause (inducedClause X R) c := by sorry

end CNFLearnMQ
