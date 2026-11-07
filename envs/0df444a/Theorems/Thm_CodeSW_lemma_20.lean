-- Prove2me | Theorems.Thm_CodeSW_lemma_20
-- name    : CodeSW.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:27:50.349496+00:00
-- url     : https://prove2.me/theorems/c4733ea1-dcb0-4256-acc8-f49744a32b09
-- title:
--   Lemma 20 — the lifts of the worm distribution are within $2^{\Delta+1}$ of $\phi$
-- statement:
--   Let $0<p<1$, let $g$ be the coupling of $h$, and let $\phi^\uparrow,\phi^\downarrow$ be the lifts of the worm distribution $\omega_g$ with $p_\uparrow=p/2$ and $p_\downarrow=(1-p)/(2-p)$. If $h$ is $\Delta$-graphic via $g$, then for every $B\subseteq E$
--   $$\phi^\uparrow(B)\le2^{\Delta+1}\phi(B).$$
--   If $h$ is $\Delta$-cographic via $g$, then for every $B\subseteq E$
--   $$\phi^\downarrow(B)\le2^{\Delta+1}\phi(B).$$
--
--   Thus enlarging the state space from even covers to the worm space costs only a factor $2^{\Delta+1}$ on the random cluster side.
--
--   Differences from the source:
--   - encoding: the ratio ϕ↑(B)/ϕ(B) ≤ 2^{∆+1} → the product form ϕ↑(B) ≤ 2^{∆+1}ϕ(B); reason: ϕ > 0 for 0 < p < 1
--   - encoding: 'If h is ∆-graphic or ∆-cographic ... respectively' → two implications: graphic gives the primal lift, cographic the dual lift, each with its own weight ratio; reason: this is what 'respectively' says; p.37 treats both lifts with these parameters
--   - encoding: ∆-graphic / ∆-cographic with coupling g (Definition 10: g the incidence matrix of a graph on m ≤ O(n) vertices; cographic through a column generator h^⊥ of col(h)^⊥) → IsDeltaGraphicVia / IsDeltaCographicVia h g ∆ for the given g, with col(h) in place of ker((h^⊥)ᵀ) and no bound on m; reason: ker((h^⊥)ᵀ) = col(h) for every column generator, and m ≤ O(n) is an asymptotic condition with no content for a single instance, while the bound here is explicit in m
--   - reading: 'edge-vertex incidence matrix of a graph' → every row of g has exactly two ones, in distinct columns (parallel edges allowed, no loops); reason: g has one edge per check with the same row index (p.21), so repeated checks of h force parallel edges; the even-subgraph and worm arguments do not use simplicity
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Lemma 20, p.21

import Definitions.Def_CodeSW_worm
import Definitions.Def_CodeSW_rc
import Definitions.Def_CodeSW_IsIncidence
open Matrix

namespace CodeSW

/-- **Lemma 20.** Let `0 < p < 1`. If `h` is ∆-graphic (∆-cographic) with primal (dual) coupling
`g`, then the primal (dual) lift of the worm distribution `ω_g` satisfies
`ϕ↑(B)/ϕ(B) ≤ 2^{∆+1}` (respectively `ϕ↓(B)/ϕ(B) ≤ 2^{∆+1}`) for every `B ⊆ E`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Lemma 20, p.21).

**Formalization Note** The ratio is written as `ϕ↑(B) ≤ 2^{∆+1} ϕ(B)` (`ϕ > 0` for `0 < p < 1`).
The worm weights use `r↑ = p↑/(1 − p↑)` with `p↑ = p/2` in the primal case and
`r↓ = p↓/(1 − p↓)` with `p↓ = (1 − p)/(2 − p)` in the dual case (p.21); "respectively" pairs
∆-graphic with the primal lift and ∆-cographic with the dual lift. -/
theorem lemma_20 {c n m Δ : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2))
    (g : Matrix (Fin c) (Fin m) (ZMod 2)) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (IsDeltaGraphicVia h g Δ → ∀ B : Finset (Fin c),
      liftUp g ((p / 2) / (1 - p / 2)) B ≤ 2 ^ (Δ + 1) * rc h p B) ∧
    (IsDeltaCographicVia h g Δ → ∀ B : Finset (Fin c),
      liftDown g (((1 - p) / (2 - p)) / (1 - (1 - p) / (2 - p))) B ≤
        2 ^ (Δ + 1) * rc h p B) := by sorry

end CodeSW
