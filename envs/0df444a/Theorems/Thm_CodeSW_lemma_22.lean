-- Prove2me | Theorems.Thm_CodeSW_lemma_22
-- name    : CodeSW.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:29:30.088463+00:00
-- url     : https://prove2.me/theorems/c8cc377e-46b1-415d-ba85-508f8769b388
-- title:
--   Lemma 22 — canonical paths through the worm space with load $\le2^\Delta m^2\omega_g(W)$
-- statement:
--   **Canonical paths through the worm space.** Let $0<p<1$, and suppose that $h$ is $\Delta$-graphic (respectively $\Delta$-cographic) and coupled to $g\in\{0,1\}^{c\times m}$. Then there is a set of canonical paths with flow function $f$ for the even cover model $\xi_\uparrow=\xi_{h,p/2}$ with cover space $\ker(h^T)$ (respectively $\xi_\downarrow=\xi_{h^\perp,(1-p)/(2-p)}$ with cover space $\mathrm{col}(h)$) through the worm space $\Omega_w$ such that, for every $W$ and every $W'=W\oplus e$,
--   $$\sum_{\gamma\ni(W,W')}f(\gamma)\le2^\Delta m^2\omega_g(W),$$
--   and in the special case $W'=W\cup e$ with $e\notin W$,
--   $$\sum_{\gamma\ni(W,W')}f(\gamma)\le2^\Delta m^2\omega_g(W)\Bigl(\frac{p_{\uparrow/\downarrow}}{1-p_{\uparrow/\downarrow}}\Bigr).$$
--
--   This is the combinatorial heart of the flow construction: even covers are connected by single-check flips through states with at most two defects, with controlled load on each flip.
--
--   Differences from the source:
--   - encoding: 'a set of canonical paths Γ and corresponding flow function f' (Definitions 14, 21) → IsWormCanonicalPaths: single-flip nonempty lists, endpoints in L, interior in Ω_w, and exactly one weighted path from I to F, of weight ξ(I)ξ(F), for all I ≠ F in L; reason: this is Definition 14 and Definition 21 together; the single flips are those of the proof on p.38
--   - encoding: '∆-graphic or ∆-cographic', with ξ↑/↓ meaning the matching model → two implications, graphic with primal and cographic with dual; reason: this is the p.21 convention for the arrows
--   - encoding: ∆-graphic / ∆-cographic with coupling g (Definition 10: g the incidence matrix of a graph on m ≤ O(n) vertices; cographic through a column generator h^⊥ of col(h)^⊥) → IsDeltaGraphicVia / IsDeltaCographicVia h g ∆ for the given g, with col(h) in place of ker((h^⊥)ᵀ) and no bound on m; reason: ker((h^⊥)ᵀ) = col(h) for every column generator, and m ≤ O(n) is an asymptotic condition with no content for a single instance, while the bound here is explicit in m
--   - reading: 'edge-vertex incidence matrix of a graph' → every row of g has exactly two ones, in distinct columns (parallel edges allowed, no loops); reason: g has one edge per check with the same row index (p.21), so repeated checks of h force parallel edges; the even-subgraph and worm arguments do not use simplicity
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Lemma 22, p.22; Definition 21, p.22; Definition 14, p.19

import Definitions.Def_CodeSW_worm
import Definitions.Def_CodeSW_evenCover
import Definitions.Def_CodeSW_IsIncidence
open Matrix
open scoped ENNReal

namespace CodeSW

/-- **Lemma 22 (Canonical paths through the worm space).** Let `0 < p < 1`, and suppose that `h`
is ∆-graphic (∆-cographic) and coupled to `g ∈ {0,1}^{c×m}`. Then there is a set of canonical
paths `Γ` with flow function `f` for the even-cover model `ξ↑ = ξ_{h,p/2}` (`ξ↓ = ξ_{h^⊥,(1−p)/(2−p)}`)
through `Ω_w` that satisfies `∑_{γ∋(W,W')} f(γ) ≤ 2^∆ m² ω_g(W)` for any `W' = W ⊕ e`, and in the
special case `W' = W ∪ e`, `∑_{γ∋(W,W')} f(γ) ≤ 2^∆ m² ω_g(W) (p↑/↓/(1 − p↑/↓))`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Lemma 22, p.22).

**Formalization Note** The primal case uses `L = Ω↑ = ker hᵀ` and `r↑ = (p/2)/(1 − p/2)`, the dual
case `L = Ω↓ = col h` and `r↓ = p↓/(1 − p↓)`, `p↓ = (1−p)/(2−p)` (p.22; `ker((h^⊥)ᵀ) = col h`).
"Canonical paths through `Ω_w`" is `IsWormCanonicalPaths` (Definitions 14 and 21); `W ∪ e` is the
special case `e ∉ W` of `W ⊕ e`. -/
theorem lemma_22 {c n m Δ : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2))
    (g : Matrix (Fin c) (Fin m) (ZMod 2)) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (IsDeltaGraphicVia h g Δ →
      ∃ f : List (Finset (Fin c)) → ℝ≥0∞,
        IsWormCanonicalPaths g (LinearMap.ker hᵀ.mulVecLin)
          (evenCover (LinearMap.ker hᵀ.mulVecLin) ((p / 2) / (1 - p / 2))) f ∧
        (∀ (W : Finset (Fin c)) (e : Fin c), stepLoad f W (symmDiff W {e}) ≤
          ENNReal.ofReal (2 ^ Δ * (m : ℝ) ^ 2 * worm g ((p / 2) / (1 - p / 2)) W)) ∧
        (∀ (W : Finset (Fin c)) (e : Fin c), e ∉ W → stepLoad f W (insert e W) ≤
          ENNReal.ofReal (2 ^ Δ * (m : ℝ) ^ 2 * worm g ((p / 2) / (1 - p / 2)) W *
            ((p / 2) / (1 - p / 2))))) ∧
    (IsDeltaCographicVia h g Δ →
      ∃ f : List (Finset (Fin c)) → ℝ≥0∞,
        IsWormCanonicalPaths g (LinearMap.range h.mulVecLin)
          (evenCover (LinearMap.range h.mulVecLin)
            (((1 - p) / (2 - p)) / (1 - (1 - p) / (2 - p)))) f ∧
        (∀ (W : Finset (Fin c)) (e : Fin c), stepLoad f W (symmDiff W {e}) ≤
          ENNReal.ofReal (2 ^ Δ * (m : ℝ) ^ 2 *
            worm g (((1 - p) / (2 - p)) / (1 - (1 - p) / (2 - p))) W)) ∧
        (∀ (W : Finset (Fin c)) (e : Fin c), e ∉ W → stepLoad f W (insert e W) ≤
          ENNReal.ofReal (2 ^ Δ * (m : ℝ) ^ 2 *
            worm g (((1 - p) / (2 - p)) / (1 - (1 - p) / (2 - p))) W *
            (((1 - p) / (2 - p)) / (1 - (1 - p) / (2 - p)))))) := by sorry

end CodeSW
