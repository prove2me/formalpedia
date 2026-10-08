-- Prove2me | Theorems.Thm_ChenSimchiLevi_General_vstar_display
-- name    : ChenSimchiLevi.General.vstar_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:29:47.379106+00:00
-- url     : https://prove2.me/theorems/a91eb586-7525-434a-a700-4bbed8196959
-- title:
--   Theorem 4.1 proof: formula for the fixed-cost ordering envelope
-- statement:
--   Let $G$ be a continuous, symmetrically $k$-concave function tending to $-\infty$ at both ends of the real line, where $k\ge0$, and let $S$ maximize $G$. Set
--   $$I=\{x\le S:G(x)\le G(S)-k\},\qquad W(x)=\sup_{y\ge x}\{G(y)-k\mathbf 1_{\{y>x\}}\}.$$
--   Then $W(x)=G(S)-k$ for $x\in I$, and $W(x)=G(x)$ otherwise. Moreover $W(x)\ge G(x)$ for every $x$, and $W(x)\ge G(S)-k$ for $x\le S$.
--
--   This is the value formula used to identify the order region and analyze the profit-to-go function.
-- source:
--   Chen, Simchi-Levi, Operations Research 52(6) (2004), p. 892, proof of Theorem 4.1, display of v*_t

import Definitions.Def_ChenSimchiLevi_General_OrderEnvelope
import Definitions.Def_ChenSimchiLevi_General_SymKConvex

set_option autoImplicit false

namespace ChenSimchiLevi.General

open Filter

/-- The display of `v*_t` in the proof of Theorem 4.1, p. 892. -/
theorem vstar_display (k : ℝ) (G : ℝ → ℝ) (hk : 0 ≤ k)
    (hGcont : Continuous G) (hGright : Tendsto G atTop atBot)
    (hGleft : Tendsto G atBot atBot)
    (hGsym : SymKConvex k (fun y => -G y))
    (S : ℝ) (hS : ∀ y, G y ≤ G S) :
    (∀ x, orderEnvelope k G x =
      if x ∈ {y | y ≤ S ∧ G y ≤ G S - k} then -k + G S else G x) ∧
    (∀ x, G x ≤ orderEnvelope k G x) ∧
    (∀ x ≤ S, -k + G S ≤ orderEnvelope k G x) := by sorry

end ChenSimchiLevi.General
