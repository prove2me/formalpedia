-- Prove2me | Theorems.Thm_BrouwerLaplacian_lemma_3_2
-- name    : BrouwerLaplacian.lemma_3_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:59:22.577206+00:00
-- url     : https://prove2.me/theorems/2d4b37a6-212f-45a5-a99a-ab21629e280d
-- title:
--   Lemma 3.2 — centered split graph nuclear norm bound $\|L_H-|K|C\|_*\le|K|\cdot|S|$
-- statement:
--   Let $H$ be a split graph on $[n]$ with clique $K$ and independent set $S=[n]\setminus K$ (edges between $K$ and $S$ are arbitrary). Let $L_H$ be its Laplacian and $C=I_n-\frac1nJ$ the centering matrix. Then
--
--   $$\|L_H-|K|\,C\|_*\le |K|\cdot|S|,$$
--
--   where $\|\cdot\|_*$ is the nuclear norm (the sum of the singular values).
--
--   This is the paper's key structural input: Brouwer's conjecture is reduced to it in Section 5, and it follows from the Grone–Merris–Bai theorem for split graphs.
--
--   **Formalization Note** The nuclear norm is the published `WainwrightHDS.NucNorm.nucNorm`, the sum of all singular values; it is not Mathlib's default entrywise matrix norm.
--
--   Differences from the source:
--   - encoding: vertex set $[n]=\{1,\dots,n\}$ → $\mathrm{Fin}\,n=\{0,\dots,n-1\}$, with $S=K^{\mathrm c}$; reason: relabeling; same instances
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, Lemma 3.2, p.2 (proof §4, p.3)

import Mathlib
import Definitions.Def_BrouwerLaplacian_centering
import Definitions.Def_BrouwerLaplacian_IsSplitWith
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm

namespace BrouwerLaplacian

open Finset

/-- **Lemma 3.2 (Centered Split Graph Nuclear Norm Bound).**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Lemma 3.2, p.2 (proof
p.3): "Let H be a split graph which has a clique K and an independent set S. The following
inequality holds ∥L_H − |K|C∥∗ ≤ |K| · |S|."

For a graph `H` on `[n]` whose vertex set splits into a clique `K` and an independent set
`S = [n] ∖ K`, the nuclear norm (sum of singular values) of `L_H − |K|·C` is at most `|K|·|S|`,
where `C = Iₙ − (1/n)J` is the centering matrix.

**Formalization Note.** Vertices are `Fin n`; `S` is `Kᶜ`. The nuclear norm is the published
`WainwrightHDS.NucNorm.nucNorm` (sum of all singular values), not Mathlib's default entrywise
matrix norm. -/
theorem lemma_3_2 {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (K : Finset (Fin n))
    (hH : IsSplitWith H K) :
    WainwrightHDS.NucNorm.nucNorm (H.lapMatrix ℝ - (#K : ℝ) • centering n)
      ≤ (#K : ℝ) * (#Kᶜ : ℝ) := by sorry

end BrouwerLaplacian
