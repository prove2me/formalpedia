-- Prove2me | Theorems.Thm_Disjunctive_NormalForms_parsimonious_mip_representation_v2
-- name    : Disjunctive.NormalForms.parsimonious_mip_representation_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:05:59.241981+00:00
-- url     : https://prove2.me/theorems/8f3ff102-74a3-46b6-8daf-7fbb6b8d70ca
-- title:
--   Theorem 4.10 — a parsimonious mixed 0-1 representation of any regular form obtained by basic steps
-- statement:
--   This is Theorem 4.10 of Balas's *Disjunctive Programming*. Let $F_0$ be a disjunctive set in conjunctive normal form (4.8), with original disjunctions $r \in T_0$ whose terms are the halfspaces $a^s x \ge a^s_0$, $s \in Q_r$, and let $F = \bigcap_{j \in T} \bigcup_{i \in Q_j} \{x : A^i x \ge b^i\}$ be a regular form (4.9) obtained from $F_0$ by basic steps: conjunct $j$ merges a set $T_{0j}$ of original disjunctions, the sets $T_{0j}$, $j \in T$, partition $T_0$, and the disjuncts $i \in Q_j$ correspond bijectively ($M_i$) to the choices of one term of every $r \in T_{0j}$, $A^i x \ge b^i$ being the system of the chosen terms. Assume each conjunct satisfies conditions (2.5)-(2.6) of Theorem 2.4. Then $F$ is the projection onto $x$ of the mixed 0-1 system
--
--   $$x = \sum_{i \in Q_j} y^i,\quad A^i y^i - b^i y^i_0 \ge 0,\quad y^i_0 \ge 0,\quad \sum_{i \in Q_j} y^i_0 = 1 \quad (j \in T),$$
--   $$\delta^r_s = \sum_{i \in Q_j:\ M_i(r) = s} y^i_0 \ (r \in T_{0j}),\qquad \sum_{s \in Q_r} \delta^r_s = 1,\qquad \delta^r_s \in \{0,1\},$$
--
--   whose binary variables $\delta^r_s$ are exactly those of the CNF $F_0$.
--
--   **Formalization Note.** The retired version (Open) did not require the sets $T_{0j}$ to partition $T_0$, which every sequence of basic steps guarantees; it was false, e.g. for $T = \emptyset$ and $T_0 \ne \emptyset$ (left side $\mathbb R^n$, right side empty since $\sum_s \delta^r_s = 0$), and with a disjunction feeding two conjuncts the linking sum double counts. The new hypothesis `hpart` states that every $r \in T_0$ feeds exactly one conjunct. Everything else is unchanged: `hChoices` (every choice of terms appears exactly once), `hPoly`, and (2.5)-(2.6) per conjunct as in the book's proof via Theorem 2.4.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §4.4, p. 59-61, Theorem 4.10

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

open Classical

/-- Theorem 4.10 (Balas, *Disjunctive Programming*, Springer 2018, §4.4, p. 59-61): let `F₀` be a
disjunctive set in CNF (4.8), with original disjunctions `r ∈ T₀` of terms `a^s x ≥ a^s_0`,
`s ∈ Q_r`, and let `F` be the same set in a regular form (4.9) obtained from `F₀` by basic steps:
each conjunct `j ∈ T` merges a set `T₀ⱼ` of original disjunctions, the sets `T₀ⱼ` partitioning
`T₀`, and each of its disjuncts `i ∈ Q_j` is the polyhedron `A^i x ≥ b^i` formed by one term of
every `r ∈ T₀ⱼ` (`M_i`), every choice of terms occurring exactly once. If every conjunct satisfies
the conditions (2.5)-(2.6) of Theorem 2.4, then `F` is the `x`-projection of the mixed 0-1
system (4.10)-(4.11), whose binary variables `δ^r_s` are those of the CNF.
Corrected: the retired version did not require the sets `T₀ⱼ` to partition `T₀` (as basic steps
produce); with an original disjunction feeding no conjunct (e.g. `T = ∅`, `T₀ ≠ ∅`) its
`δ`-constraints are infeasible, and with one feeding two conjuncts `δ` double counts. -/
theorem parsimonious_mip_representation_v2 {n : ℕ} {T0 : Type*} [Fintype T0] (Qr : T0 → Type*)
    [∀ r, Fintype (Qr r)] (a : (r : T0) → Qr r → Fin n → ℝ) (a0 : (r : T0) → Qr r → ℝ)
    {T : Type*} [Fintype T] (T0j : T → Finset T0)
    (hpart : ∀ r : T0, ∃! j : T, r ∈ T0j j) (Qj : T → Type*) [∀ j, Fintype (Qj j)]
    (mA : (j : T) → Qj j → ℕ) (A : (j : T) → (i : Qj j) → Matrix (Fin (mA j i)) (Fin n) ℝ)
    (b : (j : T) → (i : Qj j) → Fin (mA j i) → ℝ)
    (Mi : (j : T) → Qj j → (ρ : { r : T0 // r ∈ T0j j }) → Qr ρ.1)
    (hPoly : ∀ j i, Poly (A j i) (b j i) = ⋂ ρ : { r : T0 // r ∈ T0j j },
      HalfspaceGE (a ρ.1 (Mi j i ρ)) (a0 ρ.1 (Mi j i ρ)))
    (hChoices : ∀ j, Function.Bijective (Mi j))
    (h25 : ∀ (j : T) (i i' : Qj j), IsMaximalDisjunct Qj mA A b j i →
      IsMaximalDisjunct Qj mA A b j i' →
        {y : Fin n → ℝ | 0 ≤ (A j i).mulVec y} = {y : Fin n → ℝ | 0 ≤ (A j i').mulVec y})
    (h26 : ∀ (j : T) (k i : Qj j), ¬ (Poly (A j k) (b j k)).Nonempty →
      IsMaximalDisjunct Qj mA A b j i →
        {y : Fin n → ℝ | 0 ≤ (A j k).mulVec y} ⊆ {y : Fin n → ℝ | 0 ≤ (A j i).mulVec y}) :
    (⋂ j : T, ⋃ i : Qj j, Poly (A j i) (b j i)) =
      {x : Fin n → ℝ | ∃ (y : (j : T) → Qj j → Fin n → ℝ) (y0 : (j : T) → Qj j → ℝ)
        (δ : (r : T0) → Qr r → ℝ),
        (∀ j, x = ∑ i, y j i) ∧
        (∀ j i, 0 ≤ (A j i).mulVec (y j i) - y0 j i • (b j i) ∧ 0 ≤ y0 j i) ∧
        (∀ j, ∑ i, y0 j i = 1) ∧
        (∀ r s, δ r s = ∑ j : T, ∑ i : Qj j,
          if h : r ∈ T0j j then (if Mi j i ⟨r, h⟩ = s then y0 j i else 0) else 0) ∧
        (∀ r, ∑ s, δ r s = 1) ∧
        (∀ r s, δ r s = 0 ∨ δ r s = 1)} := by sorry

end Disjunctive.NormalForms
