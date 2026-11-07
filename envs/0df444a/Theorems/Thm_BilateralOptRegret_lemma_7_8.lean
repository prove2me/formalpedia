-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_7_8
-- name    : BilateralOptRegret.lemma_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:17.526817+00:00
-- url     : https://prove2.me/theorems/7130cebe-df8a-4699-8e91-8ba43def87c0
-- title:
--   Lemma 7.8 — fixed interval
-- statement:
--   Let $v_j$ be the maps of Algorithm 2. For every internal $i$ and every row $j$,
--   $$\big(\min\{z_i,z_{v_j(i)}\},\max\{z_i,z_{v_j(i)}\}\big]\subseteq(z_{i-h_i},z_{i+h_i}].$$
--   Every $(a,b)\in\mathcal I^\star$ is assigned to the interval $(z_{i-h_i},z_{i+h_i}]$ of its endpoint $i\in\{a,b\}$ of larger permitted radius; the closure of that interval contains $z_{v_j(a)}$ and $z_{v_j(b)}$ for every row $j$, and
--   $$\big(\min\{z_{v_j(a)},z_{v_j(b)}\},\max\{z_{v_j(a)},z_{v_j(b)}\}\big]\subseteq(z_{i-h_i},z_{i+h_i}].$$
--   Each such interval is assigned at most $2(\ell_K-1)$ dyadic mapped columns and one correction mapped column.
--
--   This localization underlies the bound on the cumulative mass.
--
--   Differences from the source:
--   - generalization: the sets of (17) → arbitrary sets $G_{tar},G_{qry}$; reason: only $v_j(i)\in I_i$ and the fixed boundaries are used; the sets of (17) are an instance
--   - encoding: "the endpoint with the larger permitted radius" → `assignedEnd`: the internal endpoint of larger radius; a boundary endpoint is never chosen; Lean also asserts the chosen endpoint is internal; reason: the proof, p.36, assigns a pair with a boundary endpoint to the internal one
--   - encoding: one correction mapped column per interval → the correction column of $i$ is assigned to the interval of $i$, by definition, so no Lean clause is needed; reason: each interval has a unique midpoint $i$
--   - encoding: "choose" (an arbitrary choice) → every selection rule `IsSel` on finite sets; reason: the statement holds for each way of resolving the choice by a function of the candidate set; no choice reads the law
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 7.8, p.35 (proof p.36)

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Dyadic
import Definitions.Def_BilateralOptRegret_Maps

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 7.8**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.35: fixed interval.

With `v_j` from Algorithm 2: for internal `i` and every row `j`, `(min{z_i, z_{v_j(i)}}, max{z_i, z_{v_j(i)}}] ⊆ (z_{i−h_i}, z_{i+h_i}]`. Every `(a, b) ∈ I⋆` is assigned to the interval of its endpoint `i ∈ {a, b}` of larger
permitted radius, whose closure contains `z_{v_j(a)}` and `z_{v_j(b)}` for every row `j`, and `(min{z_{v_j(a)}, z_{v_j(b)}}, max{z_{v_j(a)}, z_{v_j(b)}}]` is contained in it. Each such interval is assigned at most `2(ℓ_K − 1)`
dyadic mapped columns; its one correction mapped column is that of `i` itself.

**Formalization Note.** `assignedEnd` encodes the assignment, treating a boundary endpoint as on p.36: the internal endpoint is chosen. Lean also asserts that the assigned endpoint is internal. -/
theorem lemma_7_8 (n : ℕ) (sel : Finset (Idx n) → Idx n) (hsel : IsSel sel)
    (Gtar Gqry : Finset (Act n)) :
    (∀ i ∈ internal n, ∀ j : Idx n,
      Set.Ioc (min (z (Kof n) i) (z (Kof n) (repAfter sel Gtar Gqry (j.val + 1) i)))
          (max (z (Kof n) i) (z (Kof n) (repAfter sel Gtar Gqry (j.val + 1) i))) ⊆
        Set.Ioc (z (Kof n) (lo i)) (z (Kof n) (hiI i))) ∧
    (∀ p ∈ Istar n,
      (assignedEnd p = p.1 ∨ assignedEnd p = p.2) ∧ assignedEnd p ∈ internal n ∧
      ∀ j : Idx n,
        z (Kof n) (repAfter sel Gtar Gqry (j.val + 1) p.1) ∈
          Set.Icc (z (Kof n) (lo (assignedEnd p))) (z (Kof n) (hiI (assignedEnd p))) ∧
        z (Kof n) (repAfter sel Gtar Gqry (j.val + 1) p.2) ∈
          Set.Icc (z (Kof n) (lo (assignedEnd p))) (z (Kof n) (hiI (assignedEnd p))) ∧
        Set.Ioc
            (min (z (Kof n) (repAfter sel Gtar Gqry (j.val + 1) p.1))
              (z (Kof n) (repAfter sel Gtar Gqry (j.val + 1) p.2)))
            (max (z (Kof n) (repAfter sel Gtar Gqry (j.val + 1) p.1))
              (z (Kof n) (repAfter sel Gtar Gqry (j.val + 1) p.2))) ⊆
          Set.Ioc (z (Kof n) (lo (assignedEnd p))) (z (Kof n) (hiI (assignedEnd p)))) ∧
    ∀ i ∈ internal n, ((Istar n).filter fun p => assignedEnd p = i).card ≤ 2 * (ell n - 1) := by sorry

end BilateralOptRegret
