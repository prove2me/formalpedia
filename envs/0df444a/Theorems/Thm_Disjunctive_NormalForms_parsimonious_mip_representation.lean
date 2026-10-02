-- Prove2me | Theorems.Thm_Disjunctive_NormalForms_parsimonious_mip_representation
-- name    : Disjunctive.NormalForms.parsimonious_mip_representation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:30:47.163836+00:00
-- url     : https://prove2.me/theorems/684a69ba-d5ab-469c-aea1-02787a8e1654
-- title:
--   Theorem 4.10 — a parsimonious MIP representation of any regular form
-- statement:
--   This is Theorem 4.10 of Balas's *Disjunctive Programming*, the chapter's payoff result: any
--   disjunctive set in regular form can be represented as a mixed 0-1 program using no more binary
--   variables than its original CNF needed.
--
--   Let $F_0$ be a disjunctive set in CNF (4.8), indexed by original disjunctions $r \in T_0$ with
--   terms $s \in Q_r$, and let $F$ be the same set in a regular form (4.9) reached from $F_0$ by basic
--   steps, with conjuncts indexed by $j \in T$ and disjuncts $i \in Q_j$. Each disjunct $i$ of
--   conjunct $j$ picks exactly one term from every original disjunction $r$ feeding $j$ (recorded by
--   $M_i$). Then $F$ equals the $x$-projection of the system (4.10)-(4.11): lifted variables
--   $(y^i, y^i_0)_{i \in Q_j, j \in T}$ satisfying Theorem 2.1's construction for each conjunct, plus
--   linking constraints tying the $y^i_0$ to binary variables $\delta^r_s$ — one set of binaries *per
--   original disjunction*, not per conjunct of the (possibly much larger) regular form.
--
--   $$
--   F = \Big\{x : \exists\, y, y_0, \delta \text{ satisfying (4.10)-(4.11)}\Big\}.
--   $$
--
--   This is what makes the hull-relaxation hierarchy of Theorem 4.7 computationally practical: a
--   tighter relaxation, reached via basic steps, can always be recovered as a mixed-integer program
--   whose *integrality requirement* costs no more binary variables than the original CNF — only the
--   number of continuous lifted variables grows.
--
--   **Formalization Note.** $M_i$ (`Mi`) and the requirement that it is a bijection onto the full space
--   of term-choices (`hChoices`) together encode "every system $A_i x \ge b_i$ contains one inequality
--   per $r \in T_{0j}$, and there are as many elements of $Q_j$ as ways of choosing them" — taken as
--   given structural data relating $Q_j$ to $T_{0j}$, matching the book's own treatment of $M_i$ as a
--   named index set rather than a from-scratch construction. `hPoly` records that each conjunct's
--   polyhedron $P_i$ is literally the intersection of the chosen halfspaces, matching (4.9)'s own
--   construction of $A_i x \ge b_i$ from the original data.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 59, Theorem 4.10

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

open Classical

/-- Theorem 4.10 (Balas §4.4, p. 59-61): a disjunctive set `F` in regular form, whose conjuncts'
disjuncts each pick one inequality from every original CNF disjunction feeding it, is the
`x`-projection of the mixed 0-1 system (4.10)-(4.11), using the same number of 0-1 variables
(`δ`) as the original CNF (4.8). `T0j j` is the set of original disjunctions feeding conjunct
`j`; `Mi j i r` records which of `r`'s terms the `i`-th disjunct of conjunct `j` picked.
The page assumes `F` satisfies the conditions of Theorem 2.4, and its proof applies that theorem
to every conjunct's union `S_j`, so `(2.5)` and `(2.6)` are carried per conjunct (`h25`, `h26`).
Without them the equivalence fails: one term with `Q_r = {1,2}`, `a_1 = e_1`, `a_10 = 0`,
`a_2 = 0`, `a_20 = 1` (an empty halfspace whose recession cone is everything) has `F = {x_1 ≥ 0}`
while the right-hand side is all of `ℝⁿ`. -/
theorem parsimonious_mip_representation {n : ℕ} {T0 : Type*} [Fintype T0] (Qr : T0 → Type*)
    [∀ r, Fintype (Qr r)] (a : (r : T0) → Qr r → Fin n → ℝ) (a0 : (r : T0) → Qr r → ℝ)
    {T : Type*} [Fintype T] (T0j : T → Finset T0) (Qj : T → Type*) [∀ j, Fintype (Qj j)]
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
