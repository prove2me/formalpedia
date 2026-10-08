-- Prove2me | Theorems.Thm_ChenSimchiLevi_General_v_sym_concave
-- name    : ChenSimchiLevi.General.v_sym_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:29:48.72221+00:00
-- url     : https://prove2.me/theorems/9d2ce5b0-b006-47ce-8b81-82d3fda99bee
-- title:
--   Theorem 4.1 proof: the value function is sym-$k$-concave
-- statement:
--   Let $G$ be continuous and symmetrically $k$-concave, tend to $-\infty$ at both ends, and let $k\ge0$. If $W$ is its fixed-cost ordering envelope, then for any linear inventory coefficient $c$,
--   $$x\longmapsto cx+W(x)\quad\text{is symmetrically $k$-concave}.$$
--   This is the model-free assertion established by the four cases in the proof of Theorem 4.1(c).
-- source:
--   Chen, Simchi-Levi, Operations Research 52(6) (2004), p. 892, proof of Theorem 4.1, Cases 1–4

import Definitions.Def_ChenSimchiLevi_General_OrderEnvelope
import Definitions.Def_ChenSimchiLevi_General_SymKConvex

set_option autoImplicit false

namespace ChenSimchiLevi.General

open Filter

/-- Cases 1–4 in the proof of Theorem 4.1, p. 892. -/
theorem v_sym_concave (k : ℝ) (G : ℝ → ℝ) (hk : 0 ≤ k)
    (hGcont : Continuous G) (hGright : Tendsto G atTop atBot)
    (hGleft : Tendsto G atBot atBot)
    (hGsym : SymKConvex k (fun y => -G y)) (c : ℝ) :
    SymKConvex k (fun x => -(c * x + orderEnvelope k G x)) := by sorry

end ChenSimchiLevi.General
