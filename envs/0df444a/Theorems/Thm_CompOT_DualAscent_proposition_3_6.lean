-- Prove2me | Theorems.Thm_CompOT_DualAscent_proposition_3_6
-- name    : CompOT.DualAscent.proposition_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:49.336238+00:00
-- url     : https://prove2.me/theorems/35948e71-13a9-4477-b4b0-06ada785abc5
-- title:
--   Proposition 3.6, p. 416 — a feasible dual pair (f, g) is optimal for (3.4) or (f, g) + ε(1_S, −1_S′) is feasible and strictly better
-- statement:
--   Let $C \in \mathbb{R}^{n\times m}$ be a cost matrix and let $a \in \Sigma_n$, $b \in \Sigma_m$ be histograms (nonnegative entries summing to $1$). Consider the dual problem
--   $$\mathrm{L}_C(a,b) = \max_{(f,g)\in R(C)} \langle f, a\rangle + \langle g, b\rangle, \qquad R(C) = \{(f,g) : f_i + g_j \le C_{i,j}\ \forall i,j\},$$
--   and let $(f,g) \in R(C)$. Then either
--
--   1. $(f,g)$ is optimal for this problem, or
--   2. there exist $S \subset [\![n]\!]$ and $S' \subset [\![m]\!]'$ and $\varepsilon_0 > 0$ such that for every $0 < \varepsilon \le \varepsilon_0$ the pair $(\tilde f, \tilde g) = (f,g) + \varepsilon(\mathbb{1}_S, -\mathbb{1}_{S'})$ lies in $R(C)$ and
--   $$\langle \tilde f, a\rangle + \langle \tilde g, b\rangle > \langle f, a\rangle + \langle g, b\rangle.$$
--
--   The proposition is the engine of dual ascent methods for optimal transport: any non-optimal feasible pair of potentials admits a feasible ascent direction of the special form $(\mathbb 1_S, -\mathbb 1_{S'})$, with $0/\pm 1$ entries. With the step length of Proposition 3.5 it gives the primal-dual method, which reduces to the Hungarian algorithm on assignment problems.
--
--   **Formalization Note** Indices are 0-based (`Fin n`, `Fin m`); $\Sigma_n$ is Mathlib's `stdSimplex ℝ (Fin n)`. The book's "feasible for a small enough $\varepsilon > 0$ and has a strictly better objective" is stated as "for every $\varepsilon \in (0, \varepsilon_0]$", which is equivalent here (the objective change is linear in $\varepsilon$ and $R(C)$ is convex). The direction is restricted to the form $(\mathbb 1_S, -\mathbb 1_{S'})$ exactly as in the book; the hypothesis $(f,g) \in R(C)$ is the section's standing assumption (p. 415: "In what follows, $(f,g)$ is a feasible dual pair in $R(C)$").
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 3.6, p. 416, for Problem (3.4), p. 402

import Mathlib
import Definitions.Def_CompOT_DualAscent_Defs

namespace CompOT.DualAscent

/-- Proposition 3.6, p. 416: for histograms `a ∈ Σ_n`, `b ∈ Σ_m` and a dual feasible pair
`(f, g) ∈ R(C)`, either `(f, g)` is optimal for Problem (3.4), or there are index sets
`S ⊂ ⟦n⟧`, `S' ⊂ ⟦m⟧'` such that `(f, g) + ε (𝟙_S, -𝟙_{S'})` is dual feasible and has a strictly
larger objective for every sufficiently small `ε > 0`. -/
theorem proposition_3_6 {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (f : Fin n → ℝ) (g : Fin m → ℝ) (hfg : CompOT.Duality.dualFeasible C f g) :
    CompOT.Duality.IsDualOptimal C a b f g ∨
      ∃ (S : Finset (Fin n)) (S' : Finset (Fin m)) (ε₀ : ℝ), 0 < ε₀ ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          CompOT.Duality.dualFeasible C (f + ε • indicatorVec S) (g - ε • indicatorVec S') ∧
          CompOT.Duality.dualObj a b f g < CompOT.Duality.dualObj a b (f + ε • indicatorVec S) (g - ε • indicatorVec S') := by sorry

end CompOT.DualAscent
