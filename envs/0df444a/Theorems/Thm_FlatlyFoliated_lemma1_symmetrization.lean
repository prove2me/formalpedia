-- Prove2me | Theorems.Thm_FlatlyFoliated_lemma1_symmetrization
-- name    : FlatlyFoliated.lemma1_symmetrization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T20:42:05.597893+00:00
-- url     : https://prove2.me/theorems/2dd698f4-eddf-4e47-9ec2-4cd57c9cbd83
-- title:
--   Lemma 1 — spherical symmetrization increases $(\Delta f)^2-\|f_{ij}\|^2$
-- statement:
--   Let $\Lambda>0$ and let $f$ be smooth on $\mathbb R^3$ with $\Delta f>0$ (arrow-of-time convention), approximately spherically symmetric at infinity, and satisfying
--   $$(\Delta f)^2-\|f_{ij}\|^2=2\Lambda\quad\text{on }\mathbb R^3 .$$
--   Then its spherical symmetrization $\bar f$ satisfies
--   $$(\Delta\bar f)^2-\|\bar f_{ij}\|^2\ \ge\ 2\Lambda\quad\text{on }\mathbb R^3,$$
--   and equality holds everywhere if and only if $f$ is spherically symmetric.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, p. 17, Lemma 1 (eqs. (78)–(81))

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff

namespace FlatlyFoliated

/-- Lemma 1: symmetrization increases `(Δf)² − ‖fᵢⱼ‖²`, with equality iff `f` is
spherically symmetric. -/
theorem lemma1_symmetrization (Λ : ℝ) (hΛ : 0 < Λ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (hconv : ∀ x, 0 < lap f x) (happrox : ApproxSphSymmAtInfty f)
    (heq : ∀ x, lap f x ^ 2 - hessNormSq f x = 2 * Λ) :
    (∀ x, 2 * Λ ≤ lap (sphSymmetrization f) x ^ 2 - hessNormSq (sphSymmetrization f) x) ∧
    ((∀ x, lap (sphSymmetrization f) x ^ 2 - hessNormSq (sphSymmetrization f) x = 2 * Λ) ↔
      IsSphSymm f) := by sorry

end FlatlyFoliated
