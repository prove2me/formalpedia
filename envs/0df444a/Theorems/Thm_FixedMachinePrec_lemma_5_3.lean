-- Prove2me | Theorems.Thm_FixedMachinePrec_lemma_5_3
-- name    : FixedMachinePrec.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:38.970553+00:00
-- url     : https://prove2.me/theorems/5c51ab7b-9466-4089-9b02-1964db418846
-- title:
--   Lemma 5.3 — Algorithm 1 generates exactly $\mathcal F_k$
-- statement:
--   Let $m\ge1$, let $\prec$ be a strict partial order on $J=\{1,\dots,N\}$ and $\mathrm{rank}$ a bijective topological rank. For every $k\ge1$, the list $F_k$ stored by Algorithm 1 after layer $k$ has no repeated set, and its members are exactly the sets of $\mathcal F_k$:
--   $$\{X: X\in F_k\}=\mathcal F_k.$$
--   Moreover $\mathcal F_k$ is closed under complement relative to $J$.
--
--   For this $m$ and $k$ there is also an instance (a strict partial order with a bijective topological rank) whose $\mathcal F_k$ is not closed under union, and one whose $\mathcal F_k$ is not closed under intersection.
--
--   Algorithm 1 is thus an exact enumeration of the bounded-description family, without any schedule.
--
--   **Formalization Note** The layer is `generateFamily … k`; its set of members is compared with `family … k`.
--
--   Differences from the source:
--   - generalization: the scope m ≥ 3 of the explicit procedures (p.1) → every m ≥ 1; reason: Algorithm 1 takes integers m, K ≥ 1 (p.5) and the proof uses nothing more; m ≥ 3 is a case
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
--   - reading: “although it need not be closed under arbitrary union or intersection within the same layer” → for this m and k, an instance whose F_k is not closed under union and one whose F_k is not closed under intersection; reason: “need not be” asserts that closure can fail; it is stated at every allowed m and k, the stronger reading
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Lemma 5.3, p.13

import Mathlib
import Definitions.Def_FixedMachinePrec_GenerateFamily

namespace FixedMachinePrec

/-- **Lemma 5.3 (Exactness of the generation procedure).** Jansen, *Precedence Constraint
Scheduling on a Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Lemma 5.3, p.13: "After
layer k, the stored list F_k contains exactly F_k. In particular, each F_k is closed under
complement relative to J, although it need not be closed under arbitrary union or intersection
within the same layer."

For every `k ≥ 1`, the list stored by Algorithm 1 as layer `k` has no repeated set and its members
are exactly the sets of the family `F_k`; `F_k` is closed under complement relative to `J`; and for
this `m` and `k` there is an instance whose `F_k` is not closed under union, and one whose `F_k` is
not closed under intersection.

**Formalization Note** `J = Fin N` with a strict partial order and a bijective topological rank
(the standing setting of §2.2). "Need not be closed" is read as the existence of an instance on
which closure fails, at every `m` and `k` allowed here, the stronger reading of the clause. -/
theorem lemma_5_3 {N : ℕ} (m : ℕ) (hm : 1 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (rank : Fin N → ℕ) (hrank : IsTopoRank prec rank) (k : ℕ)
    (hk : 1 ≤ k) :
    (generateFamily prec rank m k).Nodup ∧
    (generateFamily prec rank m k).toFinset = family prec rank m k ∧
    (∀ S ∈ family prec rank m k, Finset.univ \ S ∈ family prec rank m k) ∧
    (∃ (N' : ℕ) (prec' : Fin N' → Fin N' → Prop) (_ : DecidableRel prec') (rank' : Fin N' → ℕ),
      IsStrictOrder' prec' ∧ IsTopoRank prec' rank' ∧
      ∃ X ∈ family prec' rank' m k, ∃ Y ∈ family prec' rank' m k,
        X ∪ Y ∉ family prec' rank' m k) ∧
    (∃ (N' : ℕ) (prec' : Fin N' → Fin N' → Prop) (_ : DecidableRel prec') (rank' : Fin N' → ℕ),
      IsStrictOrder' prec' ∧ IsTopoRank prec' rank' ∧
      ∃ X ∈ family prec' rank' m k, ∃ Y ∈ family prec' rank' m k,
        X ∩ Y ∉ family prec' rank' m k) := by sorry

end FixedMachinePrec
