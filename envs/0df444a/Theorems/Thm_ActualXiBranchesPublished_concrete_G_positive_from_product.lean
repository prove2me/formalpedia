-- Prove2me | Theorems.Thm_ActualXiBranchesPublished_concrete_G_positive_from_product
-- name    : ActualXiBranchesPublished.concrete_G_positive_from_product
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T09:16:28.992307+00:00
-- url     : https://prove2.me/theorems/bc4fb008-2c58-46fd-b931-b8aedd814956
-- title:
--   Positivity and normalization of the concrete xi-derived real function from its product
-- statement:
--   Let \(\xi(s)=[1+s(s-1)\Lambda_0(s)]/2\) be the concrete entire completion of zeta, and let \(G(x)=\Re\xi(1/2+\sqrt{x})\). Let \((B_i)_{i\in I}\) be indexed by a countable set, with \(\Re B_i\ge1\) and \(\sum_i(\Re B_i)^{-1}<\infty\). If
--   \[G(x)/G(0)=\prod_{i\in I}(1+x/B_i)\quad(x>0),\]
--   then \(G(x)>0\) for every \(x\ge0\), including the normalizing value \(G(0)>0\).
--   Neither positivity of G nor nonvanishing of G(0) is an assumption. The product identity and reciprocal summability remain assumptions; this theorem does not establish the Hadamard identity for xi.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno, PF28 and Branches 2/3 continuation, 2026-11-16. Classical analytic ingredients and conditional integration; no RH proof or novelty claimed. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem ActualXiBranchesPublished.concrete_G_positive_from_product (I : Type*) [Countable I] (B : I → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹)) :
    let f : ℂ → ℂ := (fun s : ℂ => (1+s*(s-1)*completedRiemannZeta₀ s)/2)
    let g : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    (∀ x > 0, ((g x / g 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i)) →
    ∀ x ≥ 0, 0 < g x := by sorry
