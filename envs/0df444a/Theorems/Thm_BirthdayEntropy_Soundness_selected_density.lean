-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_selected_density
-- name    : BirthdayEntropy.Soundness.selected_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:50:47.08609+00:00
-- url     : https://prove2.me/theorems/e3902819-adf1-4c68-b381-b6a99bead809
-- title:
--   Corollary 4.10 — Logarithmic-cubic birthday soundness
-- statement:
--   For each real $d\ge1,\varepsilon>0$ there are uniform $C_0,c>0$ and $0<x_0<1/2$ such that for every source in the NO class, every admitted scale $2\le\ell\le x_0n$ with $\ell\log(en/\ell)\ge C_0\log(n+1)$, and every set $H$ of exactly $K=\binom n\ell$ distinct birthday vertices,
--   $$\rho(H)\le2\exp\!\left(-c\frac{nx^3}{\log(e/x)}\right),\qquad x=\ell/n.$$
--   Here $\rho(H)=|E(H)|/\binom K2$, including arbitrary missing views, multiple labels per view and isolated locally invalid labels. Constants precede every instance, scale and selection. This is the pointwise density form of the main soundness result.
--
--   Differences from the source:
--   - encoding: variables [n] and indexed constraints with arbitrary ternary Boolean predicates → Fin n, Fin m and the published RandOrderCSP.CSP 3 Bool with injective scope rows; reason: reindexing and ordering each three-element scope changes no instance or predicate; repeated scopes remain distinct indices
--   - encoding: standing section scale thresholds → existential C0,x0 explicitly quantified before instances; reason: the thresholds depend only on d,epsilon and encode the same standing assumptions
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Corollary 4.10, PDF pp15 / printed pp14

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Graph

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- Corollary 4.10 (19), PDF p15 / printed p14. Every selected set of
K distinct vertices, including repeated views, missing views and isolated labels. -/
theorem selected_density (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε) :
    ∃ C₀ c x₀ : ℝ, 0 < C₀ ∧ 0 < c ∧ 0 < x₀ ∧ x₀ < 1/2 ∧
      ∀ (n m : ℕ) (φ : CSP n m), Source φ d → Gap φ ε →
      ∀ (ℓ : ℕ), Admitted n ℓ C₀ x₀ →
      ∀ (H : Finset (Vertex n ℓ)), H.card = Nat.choose n ℓ →
        density φ H ≤ 2 * Real.exp (-c * n * (ratio n ℓ)^3 / logScale n ℓ) := by sorry

end BirthdayEntropy.Soundness
