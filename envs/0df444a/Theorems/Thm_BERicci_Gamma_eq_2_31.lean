-- Prove2me | Theorems.Thm_BERicci_Gamma_eq_2_31
-- name    : BERicci.Gamma.eq_2_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:05.271993+00:00
-- url     : https://prove2.me/theorems/e2b8b247-49fc-41d1-a9d3-3db3f6566f0d
-- title:
--   (2.31), p. 18 — a(τ) − a(0) + ν∫₀^τ I_{−2K}(s)g(s)ds ≤ a′(τ)I_{−2K}(τ)
-- statement:
--   Let $t>0$, $K\in\mathbb R$, $\nu\ge0$, $a\in C^1([0,t))$ with derivative $a'$, and $g\in C^0([0,t))$, and suppose $a''\ge2Ka'+\nu g$ in $\mathscr D'(0,t)$ (and pointwise when $a\in C^2([0,t))$), i.e. condition (i) of Lemma 2.2. Write $I_K(\tau)=\int_0^\tau e^{Ks}\,ds$, so that $I_K(\tau)=(e^{K\tau}-1)/K$ for $K\ne0$ and $I_0(\tau)=\tau$. Then for every $\tau\in[0,t)$
--
--   $$a(\tau)-a(0)+\nu\int_0^\tau I_{-2K}(s)\,g(s)\,ds\le a'(\tau)\,I_{-2K}(\tau).\tag{2.31}$$
--
--   The paper obtains it from (2.27) with $\zeta(s)=I_{-2K}(s)=(1-e^{-2Ks})/(2K)$. With $a=\mathsf A_t[f;\varphi]$ it yields the local Poincaré-type estimate (v) of Corollary 2.3.
--
--   **Formalization Note** $I_{-2K}$ is $I_K$ evaluated at $-2K$ (not $-I_{2K}$).
-- source:
--   arXiv:1209.5786v4, (2.31), p. 18

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Gamma_Calculus

namespace BERicci.Gamma

open MeasureTheory Topology
open scoped ENNReal

/-- (2.31), p. 18: under Lemma 2.2 (i), `a(τ) − a(0) + ν ∫₀^τ I_{−2K}(s) g(s) ds ≤ a'(τ) I_{−2K}(τ)`
for every `τ ∈ [0,t)`. -/
theorem eq_2_31 (K ν t : ℝ) (ht : 0 < t) (hν : 0 ≤ ν)
    (a ap g : ℝ → ℝ) (ha : IsC1Ico t a ap) (hg : ContinuousOn g (Set.Ico 0 t))
    (h : L22Cond1 K ν t a ap g) :
    ∀ τ ∈ Set.Ico 0 t,
      a τ - a 0 + ν * ∫ s in (0 : ℝ)..τ, IK (-2 * K) s * g s
        ≤ ap τ * IK (-2 * K) τ := by sorry

end BERicci.Gamma
