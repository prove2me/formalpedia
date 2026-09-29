-- Prove2me | Theorems.Thm_FoundationsML_MaxEnt_maxent_duality
-- name    : FoundationsML.MaxEnt.maxent_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-20T04:18:57.642778+00:00
-- url     : https://prove2.me/theorems/407c7b0d-a7f9-43e1-b922-fc109e927c1d
-- title:
--   Theorem 12.2 — Maxent duality (goal)
-- statement:
--   **Statement (Theorem 12.2, Maxent duality, p. 300, PDF p. 317).** Problems (12.7) or (12.8)
--   are equivalent to the optimization problem $\sup_{w\in\mathbb R^N}G(w)$:
--   $$\sup_{w\in\mathbb R^N}G(w) = \min_p F(p).$$
--   Furthermore, let $p^*=\arg\min_pF(p)$ and $d^*=\sup_{w\in\mathbb R^N}G(w)$; then, for any
--   $\epsilon>0$ and any $w$ such that $|G(w)-d^*|<\epsilon$, $D(p^*\|p_w)\le\epsilon$.
--
--   This is the chapter's capstone: it shows that the Maxent principle's primal optimization
--   (an entropy-maximization / relative-entropy-minimization problem over distributions) is
--   exactly dual to a regularized maximum-likelihood problem over the family of Gibbs
--   distributions — explaining why the (seemingly unrelated) Maxent principle always produces
--   a Gibbs-form solution, and giving an $\epsilon$-solution-of-the-dual $\Rightarrow$
--   $\epsilon$-close-primal-distribution guarantee that makes solving the (often easier,
--   unconstrained, finite-dimensional) dual problem a valid way to solve the primal.
--
--   **Formalization Note.** This is the sharpest trivialization risk of the whole series:
--   the equality is *not* an unconditional convex-duality fact, and both clauses (the `sup=min`
--   equality and the `D(p*‖p_w)≤ε` approximation guarantee) are drafted as a conjunction, per
--   `BRIEF.md`'s explicit warning that the second clause is easy to drop by accident. `hlam :
--   0 < λ` is a genuine load-bearing hypothesis (the book's own proof uses `λ>0` to place `u₀`
--   in the interior of `C`, invoking the qualification condition of the book's own Theorem
--   B.39/Fenchel duality theorem) — not a free convexity assumption, and dropping it would
--   misstate the theorem. `F`'s `EReal` codomain and the explicit `IsLeast` hypothesis for `p*`
--   are used exactly as `MaxEntPrimalObjective` and the dual-objective supremum are defined.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 300, Theorem 12.2 (PDF p. 317)

import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_MaxEntPrimalObjective
import Definitions.Def_FoundationsML_MaxEnt_MaxEntDualObjective
import Definitions.Def_FoundationsML_MaxEnt_RelativeEntropy
import Definitions.Def_FoundationsML_MaxEnt_GibbsDistribution

namespace FoundationsML.MaxEnt

/-- Theorem 12.2 (Maxent duality; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 300, PDF p. 317 — this mission's goal). Problems (12.7)
or (12.8) are equivalent to the optimization problem `sup_{w∈ℝ^N} G(w)`:
`sup_{w∈ℝ^N} G(w) = min_p F(p)`. Furthermore, let `p* = argmin_p F(p)` and
`d* = sup_{w∈ℝ^N} G(w)`; then, for any `ε > 0` and any `w` such that `|G(w) − d*| < ε`,
`D(p* ‖ p_w) ≤ ε`.

**Formalization Note.** The equality is stated in `EReal` (matching `MaxEntPrimalObjective`'s
own `EReal` codomain, since `F` can take the value `+∞`); `sup_w G(w)` is a real (`ℝ`) real
supremum (`⨆`, a Mathlib `iSup` over a conditionally complete lattice, matching the standing
well-definedness convention already used for suprema throughout this series, e.g. chunk
`05-svm`'s `EmpiricalRademacherComplexity`), coerced into `EReal` for the comparison; `min_p
F(p)` is `sInf (Set.range (MaxEntPrimalObjective …))`, `EReal`'s own infimum (a complete
lattice). The hypothesis `hlam : 0 < λ` matches the book's own use of `λ > 0` in its proof (to
place `u₀` in the interior of `C`, invoking the qualification condition of Theorem B.39) — not
a free choice, dropping it would prove a materially different (and, per `BRIEF.md`'s named
trivialization trap, potentially false) statement than the book's own conditional duality
claim. `p*` is quantified by an explicit `IsLeast` hypothesis (the standard Lean idiom for "let
`p*` be a/the minimizer") rather than assumed to exist unconditionally. -/
theorem maxent_duality {X : Type*} [Fintype X] {N : ℕ}
    (p0 : X → ℝ) (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hΦ : ∀ x j, |Φ x j| ≤ r)
    (m : ℕ) (hm : 0 < m) (S : Fin m → X) (lam : ℝ) (hlam : 0 < lam) :
    (↑(⨆ w : Fin N → ℝ, MaxEntDualObjective p0 Φ S lam w) : EReal) =
        sInf (Set.range (MaxEntPrimalObjective p0 Φ S lam)) ∧
      ∀ p_star : X → ℝ,
        IsLeast (Set.range (MaxEntPrimalObjective p0 Φ S lam)) (MaxEntPrimalObjective p0 Φ S lam p_star) →
        ∀ ε : ℝ, 0 < ε → ∀ w : Fin N → ℝ,
          |MaxEntDualObjective p0 Φ S lam w -
              ⨆ w' : Fin N → ℝ, MaxEntDualObjective p0 Φ S lam w'| < ε →
            RelativeEntropy p_star (GibbsDistribution p0 Φ w) ≤ ε := by sorry

end FoundationsML.MaxEnt
