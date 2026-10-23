-- Prove2me | Theorems.Thm_CustomerVoice_OLearn_proposition_3
-- name    : CustomerVoice.OLearn.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:08:17.758842+00:00
-- url     : https://prove2.me/theorems/aea80fd9-e1bd-4ddf-9414-94d2e50b1f7e
-- title:
--   Proposition 3, p. 17 — the cheap-signaling separating equilibrium under O-Learning exists iff θH/θL ≥ Λ
-- statement:
--   Consider the O-Learning game under the standing assumptions $\theta_H>\theta_L>0$, $\alpha,\gamma\in(0,1)$, $k,s>0$. Let $q^O_H=q^*(\theta_H)$ and $q^O_L=q^*(\theta_L)$ with $q^*(\theta)=\min\{\gamma\theta/(s+\gamma k),\theta/(2k)\}$, and let
--   $$\Lambda=\max\{\min\{\Lambda_{H1},\Lambda_{H2}\},\Lambda_L\},\quad \Lambda_{H1}=\frac{\gamma(s+k)}{(1-\gamma)s},\ \Lambda_{H2}=\frac{1+\gamma}{1-\gamma},\ \Lambda_L=\frac{s}{\gamma k}.$$
--   Then:
--   1. there is a belief function $\hat\theta(\cdot)$ under which the requests $(q^O_H,q^O_L)$ form a separating equilibrium if and only if
--   $$\frac{\theta_H}{\theta_L}\ge\Lambda;$$
--   2. if $\theta_H/\theta_L\ge\Lambda$ and $\gamma\le s/k$, the requests form a separating equilibrium with beliefs $\hat\theta(q^O_H)=\theta_H$, $\hat\theta(q^O_L)=\theta_L$ and $\hat\theta(q)=\theta_L$ for every other $q$;
--   3. if $\theta_H/\theta_L\ge\Lambda$ and $\gamma\ge s/k$, the requests form a separating equilibrium with beliefs $\hat\theta(q^O_H)=\theta_H$, $\hat\theta(q^O_L)=\theta_L$ and $\hat\theta(q)=\theta_H$ for every other $q$.
--
--   In the "only if" direction of item 1 the belief function is arbitrary, off the equilibrium path included. The result says that buyers who design their own products can reveal their preferences while asking for their full-information optima exactly when the two types differ enough.
--
--   **Formalization Note** The equilibrium is a pure-strategy separating perfect Bayesian equilibrium: nonnegative distinct requests, on-path consistent beliefs, and no profitable deviation to any request $q\ge0$. The seller accepts iff $\gamma(\hat\theta q-kq^2)-sq^2\ge0$ under its belief, accepting at a tie as printed, and a rejected request pays $0$. The price stage enters only in reduced form through (9). At $\gamma=s/k$ both belief functions support the equilibrium.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 17, Proposition 3

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

namespace CustomerVoice.OLearn

theorem proposition_3 (M : Model) (hM : M.Standing) :
    ((∃ bel : ℝ → CustomerVoice.ALearn.BType, M.OSepEq M.qO bel) ↔ M.θH / M.θL ≥ M.Lambda) ∧
    (M.θH / M.θL ≥ M.Lambda → M.γ ≤ M.s / M.k → M.OSepEq M.qO M.belLow) ∧
    (M.θH / M.θL ≥ M.Lambda → M.s / M.k ≤ M.γ → M.OSepEq M.qO M.belHigh) := by sorry

end CustomerVoice.OLearn
