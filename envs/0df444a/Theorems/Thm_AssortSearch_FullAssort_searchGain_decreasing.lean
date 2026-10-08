-- Prove2me | Theorems.Thm_AssortSearch_FullAssort_searchGain_decreasing
-- name    : AssortSearch.FullAssort.searchGain_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:51.35436+00:00
-- url     : https://prove2.me/theorems/5d8b1a36-7ac2-48d6-8807-4e9161f956c0
-- title:
--   Proof of Theorem 3, p. 11 — the left-hand side of (5) is decreasing in $y$
-- statement:
--   Let $\mu > 0$, let $v_1, \dots, v_n > 0$, and let $S \subsetneq N$, so that $\bar S = N - S$ is nonempty. For a consumer whose best utility in the store is $y$, the expected incremental gain from search is the left-hand side of (5),
--
--   $$\Phi_S(y) = \int_y^\infty (\bar y - y)\, w(\bar y, S)\, d\bar y .$$
--
--   Then for every $y$ the integrand is integrable on $(y, \infty)$, and $\Phi_S$ is strictly decreasing in $y$.
--
--   The paper states this in the proof of Theorem 3 and uses it to conclude that the search threshold $\bar U(S)$ is unique.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 11 (PDF 13), proof of Theorem 3, (5)

import Mathlib
import Definitions.Def_AssortSearch_FullAssort_Model

namespace AssortSearch.FullAssort

/-- Proof of Theorem 3 (p. 11): for an assortment `S ⊊ N`, the left-hand side of (5),
`Φ_S(y) = ∫_y^∞ (ȳ − y) w(ȳ, S) dȳ`, is a convergent integral for every `y` and is
(strictly) decreasing in `y`. -/
theorem searchGain_decreasing {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    (∀ y : ℝ, MeasureTheory.IntegrableOn (fun t => (t - y) * w μ v S t) (Set.Ioi y)) ∧
      StrictAnti (searchGain μ v S) := by sorry

end AssortSearch.FullAssort
