-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_Supplement_lemma_16
-- name    : FacilityIncompatibilities.UniformMatroid.Supplement.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:13:23.654299+00:00
-- url     : https://prove2.me/theorems/33955a6b-0bfd-48a7-9ad9-c401578b9446
-- title:
--   Lemma 16 — simultaneous subset bound for the greedy eight-slot map
-- statement:
--   Let $d$ be a (pseudo)metric on the facilities, let $P,O$ be finite facility sets with $|P|\le|O|$, put $Q:=P\cap O$, and let $\nu:P\to O$ be any output of the greedy eight-slot construction of §4.1 (with any tie-breaking). Then, for every subset $T\subseteq P$ simultaneously,
--
--   $$\sum_{s\in T}\min\{d(s,\nu(s)),\ \mathrm{dist}(s,P\setminus T)\}\ \le\ 6\,\mathrm{mc}(T,O),\tag{10}$$
--
--   where $\mathrm{dist}(s,\emptyset):=+\infty$ and $\mathrm{mc}(T,O)$ is the minimum total distance of an injection $T\to O$. Moreover:
--
--   1. $\nu(q)=q$ for every $q\in Q$;
--   2. every $s\in P\setminus Q$ is mapped into $O\setminus Q$ (no other point maps to $Q$);
--   3. every $o\in O\setminus Q$ has at most eight preimages in $P$.
--
--   The map $\nu$ is fixed before $T$ is chosen; the same map serves every group-specific subset in the test-swap analysis of Theorem 4, which is why the bound must hold for all $T$ at once.
--
--   **Formalization Note** The sum, the minimum, $\mathrm{dist}$ and $\mathrm{mc}$ are in `ℝ≥0∞`. A greedy output is described by its order of assignment (the predicate `IsGreedyMap`). The instance's clients and matroid play no role.
--
--   Differences from the source:
--   - generalization: P = π(V_C) ∪ (S ∩ O) and O an optimal facility set, built in §4.1 from a local optimum S → arbitrary finite facility sets P, O with |P| ≤ |O|; reason: the construction and the proof use only Q = P ∩ O and |P| ≤ |O|, which the paper establishes for its P, so the paper's case is an instance
--   - generalization: metric distances d (Definition 1) → a pseudometric (distinct points may be at distance 0); reason: every metric satisfies these axioms
--   - encoding: the map ν constructed above, ties arbitrary → any ν satisfying IsGreedyMap (an assignment order in which each step takes a globally shortest eligible pair); reason: these are exactly the outputs of the greedy procedure under all tie-breaking rules
--   - encoding: ν : P → O and "no other point maps to Q" → ν : F → F with ν s ∈ O and ν s ∉ Q for s ∈ P \ Q, preimages counted in P; reason: states the codomain of ν explicitly; values outside P are irrelevant
--   - encoding: real-valued sums, min, dist with dist(s, ∅) = +∞, and mc as a minimum over injections → ℝ≥0∞ values, dist as an infimum (⊤ on ∅), mc as an infimum over injections (⊤ if none); reason: distances are nonnegative, and a minimum over a finite nonempty set is the infimum
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Lemma 16, eq. (10), printed p.15 / PDF p.16; construction of ν and mc(T, O), §4.1, printed pp.14–15 / PDF pp.15–16

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Supplement_Congestion

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid.Supplement

/-- **Lemma 16** (Simultaneous subset bound; printed p.15 / PDF p.16). Let `P, O` be finite
facility sets with `|P| ≤ |O|`, `Q = P ∩ O`, and let `ν` be any output of the greedy eight-slot
construction of §4.1. Then, for every subset `T ⊆ P` simultaneously,
`∑_{s ∈ T} min{d(s, ν(s)), dist(s, P \ T)} ≤ 6 mc(T, O)` (10), with `dist(s, ∅) = +∞`.
Moreover `ν(q) = q` for `q ∈ Q`, every other point of `P` maps into `O \ Q`, and every
`o ∈ O \ Q` has at most eight preimages in `P`. -/
theorem lemma_16 {C F : Type*} [DecidableEq F] (I : Instance C F) (hI : I.Valid)
    (P O : Finset F) (hPO : P.card ≤ O.card) (ν : F → F) (hν : IsGreedyMap I P O ν) :
    (∀ T ⊆ P, ∑ s ∈ T, min (ENNReal.ofReal (I.fdist s (ν s))) (setDist I s (P \ T)) ≤
        6 * mc I T O) ∧
    (∀ q ∈ P ∩ O, ν q = q) ∧
    (∀ s ∈ P \ (P ∩ O), ν s ∈ O ∧ ν s ∉ P ∩ O) ∧
    (∀ o ∈ O \ (P ∩ O), (P.filter fun s => ν s = o).card ≤ 8) := by sorry

end FacilityIncompatibilities.UniformMatroid.Supplement
