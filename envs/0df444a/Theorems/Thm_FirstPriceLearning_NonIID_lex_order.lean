-- Prove2me | Theorems.Thm_FirstPriceLearning_NonIID_lex_order
-- name    : FirstPriceLearning.NonIID.lex_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:00.784622+00:00
-- url     : https://prove2.me/theorems/5941b003-0699-4bc6-bdd8-574e2dcfdb74
-- title:
--   Proof of Theorem 8, p. 34 — lexicographic order: $f(\dots,u_{t-1},1,\dots)>f(\dots,u_{t-1},-1,u'_{t+1},\dots)$
-- statement:
--   Let $f(u)=\frac12+\frac14\sum_{s=1}^T u_s/2^s$ for $u\in\{\pm1\}^T$. Let $t\in[T]$ and let $u,u'\in\{\pm1\}^T$ agree in rounds $1,\dots,t-1$, with $u_t=1$ and $u'_t=-1$. Then
--   $$
--   f(u_1,\dots,u_{t-1},1,u_{t+1},\dots,u_T)>f(u_1,\dots,u_{t-1},-1,u'_{t+1},\dots,u'_T),
--   $$
--   whatever the later signs $u_{t+1},\dots,u_T$ and $u'_{t+1},\dots,u'_T$.
--
--   The order means that the first round in which two thresholds differ decides which is larger. It is the reason the value $v_t$, built from $u_1,\dots,u_{t-1}$, falls on the side of the threshold chosen by $u_t$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 34, proof of Theorem 8, display after the definition of f

import Mathlib
import Definitions.Def_FirstPriceLearning_NonIID_HardInstance

namespace FirstPriceLearning.NonIID

/-- Proof of Theorem 8, arXiv:2003.09795v7, p. 34 (display after the definition of `f`): the
lexicographic order of `f(u) = 1/2 + (1/4) ∑_{s=1}^T u_s / 2^s` on sign vectors. If `u, u' ∈ {±1}^T`
agree before round `t`, and `u_t = 1`, `u'_t = −1`, then `f(u) > f(u')`, whatever the later signs. -/
theorem lex_order (T : ℕ) (t : Fin T) (u u' : Fin T → ℝ)
    (hu : ∀ s, u s = 1 ∨ u s = -1) (hu' : ∀ s, u' s = 1 ∨ u' s = -1)
    (hprefix : ∀ s : Fin T, s < t → u s = u' s) (ht : u t = 1) (ht' : u' t = -1) :
    fval u' < fval u := by sorry

end FirstPriceLearning.NonIID
