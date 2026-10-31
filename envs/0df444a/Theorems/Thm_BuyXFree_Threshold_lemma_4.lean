-- Prove2me | Theorems.Thm_BuyXFree_Threshold_lemma_4
-- name    : BuyXFree.Threshold.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:36.054637+00:00
-- url     : https://prove2.me/theorems/d0a6158a-72e2-48b8-8ae1-f442fa892a9a
-- title:
--   Lemma 4, p. 36 — v + k + δJ(0) ≥ δJ(X): with outside option 0 the consumer always redeems
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. $J$ denotes any solution of the optimality equations (1)–(2) of the consumer facing price $p$ and threshold $X$. For every price $p$,
--   $$v+k+\delta J(0)\ \ge\ \delta J(X).$$
--
--   That is, a consumer holding $X$ points always redeems when the outside option is $0$.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 36, Lemma 4 (stated in the proof of Proposition 2)

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Lemma 4, p. 36: `v + k + δJ(0) ≥ δJ(X)`; with outside option `0` the consumer always
redeems. -/
theorem lemma_4 (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (hX : 1 ≤ X)
    (J : ℕ → ℝ) (hJ : IsValueFn P p X J) :
    P.v + P.k + P.δ * J 0 ≥ P.δ * J X := by sorry
end BuyXFree.Threshold
