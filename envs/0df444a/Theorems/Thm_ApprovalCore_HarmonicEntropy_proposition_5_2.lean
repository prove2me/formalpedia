-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_proposition_5_2
-- name    : ApprovalCore.HarmonicEntropy.proposition_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:31:27.131842+00:00
-- url     : https://prove2.me/theorems/315c1880-ba1f-4bd1-b0aa-092e544b749c
-- title:
--   Proposition 5.2 — $F$ is continuous, concave, symmetric and invariant under adding zero coordinates
-- statement:
--   Harmonic entropy $F$ has the following four properties, for every dimension $d$.
--   1. $F$ is continuous on $\Delta_d$.
--   2. $F$ is concave on $\Delta_d$: $F(\lambda x + (1-\lambda) x') \ge \lambda F(x) + (1-\lambda) F(x')$ for $x, x' \in \Delta_d$, $\lambda \in [0,1]$.
--   3. $F$ is symmetric: $F(x \circ \sigma) = F(x)$ for every $x \in \Delta_d$ and every permutation $\sigma$ of the coordinates.
--   4. $F$ is invariant under adding zero coordinates: if $y \in \mathbb R^{d'}$ is obtained from $x \in \Delta_d$ by inserting zero coordinates (at any positions), then $F(y) = F(x)$.
--
--   These properties make $V(W)$ a maximum of a continuous concave function over a compact convex set and justify the coordinate manipulations in Theorems 6.2, 6.3 and Lemma 6.4.
--
--   **Formalization Note.** Item 4 is stated for every injection $e : [d] \hookrightarrow [d']$ and every $y$ with $y_{e(j)} = x_j$ and $y_{j'} = 0$ off the range of $e$.
--
--   Differences from the source:
--
--   - encoding: a distribution x ∈ ∆_d with coordinates indexed by [d] → x : Fin d → ℝ with x ∈ stdSimplex ℝ (Fin d), coordinates indexed 0, …, d−1; reason: Mathlib's standard simplex is exactly ∆_d (nonnegative coordinates summing to 1); only the index base changes
--   - encoding: F continuous, concave → ContinuousOn and ConcaveOn ℝ on stdSimplex ℝ (Fin d), for every d; reason: F is a function on distributions; ∆_d is its domain
--   - reading: invariant under adding zero coordinates (positions unspecified) → F y = F x whenever y is x with zeros inserted at arbitrary positions (any embedding Fin d ↪ Fin d'); reason: the paper does not say where the zeros go; the reading 'at any positions' is the stronger one and is how the property is used (p. 13, p. 14: dropping a zero reserve coordinate)
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 11 (PDF 12), Proposition 5.2; proof p. 34 (PDF 35)

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_RobinHood

namespace ApprovalCore.HarmonicEntropy

/-- Proposition 5.2 (p. 11): `F` is continuous and concave on `∆d`, symmetric (invariant
under coordinate permutations) and invariant under adding zero coordinates (at any
positions). -/
theorem proposition_5_2 :
    (∀ d : ℕ, ContinuousOn (harmonicEntropy (d := d)) (stdSimplex ℝ (Fin d))) ∧
    (∀ d : ℕ, ConcaveOn ℝ (stdSimplex ℝ (Fin d)) (harmonicEntropy (d := d))) ∧
    (∀ (d : ℕ) (σ : Equiv.Perm (Fin d)) (x : Fin d → ℝ), x ∈ stdSimplex ℝ (Fin d) →
      harmonicEntropy (x ∘ σ) = harmonicEntropy x) ∧
    (∀ (d d' : ℕ) (e : Fin d ↪ Fin d') (x : Fin d → ℝ) (y : Fin d' → ℝ),
      x ∈ stdSimplex ℝ (Fin d) → (∀ j, y (e j) = x j) →
      (∀ j', j' ∉ Set.range e → y j' = 0) → harmonicEntropy y = harmonicEntropy x) := by sorry

end ApprovalCore.HarmonicEntropy
