-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_corollary_2_2
-- name    : BourgainUnion.Euclidean.corollary_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:17.000007+00:00
-- url     : https://prove2.me/theorems/9da61c5c-ef28-43e1-bcf1-9faa13c994a8
-- title:
--   Corollary 2.2 — collapse above a Hilbert subspace
-- statement:
--   Choose one pair of positive constants $a,b$ valid for Lemma 2.1. They can be chosen so that for every finite- or countably-dimensional real Hilbert space $H$ there is $\psi:H\times\mathbb R\to\ell_2$ with $\psi(u,0)=0$ for every $u$, and for all $u,v\in H$ and $h,j\ge0$,
--   $$\frac a{\sqrt2}\min\{\|u-v\|+|h-j|,h+j\}\le\|\psi(u,h)-\psi(v,j)\|\le b\min\{\|u-v\|+|h-j|,h+j\}.$$
--   This keeps the same dimension-independent constants as the preceding collapse result. It supplies the maps used to suppress Voronoi components at cell boundaries.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - generalization: absolute Θ constants in the corollary → the inherited lower constant a/√2 and upper constant b, with CollapseConstants a b also concluded; reason: the Hilbert norm of a pair lies between its l1 norm divided by √2 and its l1 norm; the hyperplane distance is the absolute height; the explicit form implies the source's asymptotic statement
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 5, Corollary 2.2

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_VoronoiModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Corollary 2.2 with constants inherited coherently from Lemma 2.1. -/
theorem corollary_2_2 : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ CollapseConstants a b ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
      ∃ ψ : H → ℝ → H2, HyperplaneCollapse (a / Real.sqrt 2) b ψ := by sorry

end BourgainUnion.Euclidean
