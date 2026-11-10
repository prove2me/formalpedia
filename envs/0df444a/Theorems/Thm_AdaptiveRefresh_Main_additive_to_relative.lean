-- Prove2me | Theorems.Thm_AdaptiveRefresh_Main_additive_to_relative
-- name    : AdaptiveRefresh.Main.additive_to_relative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:01:10.261655+00:00
-- url     : https://prove2.me/theorems/61f0e54d-4fbc-4d39-a1d2-e4d106391661
-- title:
--   Property 3.1 — additive to relative approximation
-- statement:
--   Let $G$ be a nontrivial loopless weighted graph on $n$ vertices and $H$ a reweighted same-vertex subgraph. Suppose $\phi,\Delta,\rho>0$, $\epsilon>0$, $\eta\ge0$, every nonempty proper cut has conductance at least $\phi$, and each degree lies in $[\Delta/\rho,\Delta]$. If
--
--   $$\eta\le\frac{\phi^2\epsilon}{2\rho},\qquad\|L_H-L_G\|\le\eta\Delta,$$
--
--   then for every real vector $x$,
--
--   $$(1-\epsilon)x^\top L_Gx\le x^\top L_Hx\le(1+\epsilon)x^\top L_Gx.$$
--
--   This converts an additive operator-norm error into the source's exact relative spectral approximation. Support is retained by the subgraph hypothesis.
--
--   Differences from the source:
--   - encoding: a φ-expander with degrees in [Δ/ρ,Δ] and a reweighted subgraph H → all nonempty proper cuts satisfy the conductance lower bound; positive φ,Δ,ρ and at least two vertices; H retains input support; reason: these spell out the nondegenerate expander application, with no assumed spectral gap
--   - reading: accuracy parameters η and ε → ε>0 and η≥0; reason: positivity is the accuracy convention; zero additive error is included and forces equality of the two Laplacians
--   - encoding: H is a (1±ε)-spectral sparsifier → both exact quadratic inequalities via the published predicate, with support already a hypothesis; reason: this preserves the source approximation convention instead of the reciprocal-σ convention
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Property 3.1, printed p. 5 (PDF p. 6). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_Graph

set_option autoImplicit false

namespace AdaptiveRefresh.Main

/-- Property 3.1, printed p. 5 / PDF p. 6. Conductance is stated directly as a
lower bound over all nonempty proper cuts, with positive degrees. -/
theorem additive_to_relative (n : ℕ) (G H : Graph) (φ Δ ρ η ε : ℝ)
    (hn : 2 ≤ n) (hG : ValidGraph n G) (hH : ReweightedSubgraph n G H)
    (hφ : 0 < φ) (hΔ : 0 < Δ) (hρ : 0 < ρ) (hε : 0 < ε) (hη : 0 ≤ η)
    (hexp : Expander n φ G)
    (hdegrees : ∀ v : Fin n, Δ / ρ ≤ degree n G v ∧ degree n G v ≤ Δ)
    (hscale : η ≤ φ ^ 2 * ε / (2 * ρ))
    (herror : opNorm (laplacian n H - laplacian n G) ≤ η * Δ) :
    SpectralApprox n ε G H := by sorry

end AdaptiveRefresh.Main
