-- Prove2me | Theorems.Thm_BERicci_Gamma_eq_2_30
-- name    : BERicci.Gamma.eq_2_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:35.101998+00:00
-- url     : https://prove2.me/theorems/b6369482-5676-453d-9e0a-98811387a1dd
-- title:
--   (2.30), p. 18 — I_{2K}(τ)a′(0) + ν∫₀^τ I_{2K}(τ−s)g(s)ds ≤ a(τ) − a(0)
-- statement:
--   Let $t>0$, $K\in\mathbb R$, $\nu\ge0$, $a\in C^1([0,t))$ with derivative $a'$, and $g\in C^0([0,t))$, and suppose $a''\ge2Ka'+\nu g$ in $\mathscr D'(0,t)$ (and pointwise when $a\in C^2([0,t))$), i.e. condition (i) of Lemma 2.2. Write $I_K(\tau)=\int_0^\tau e^{Ks}\,ds$, so that $I_K(\tau)=(e^{K\tau}-1)/K$ for $K\ne0$ and $I_0(\tau)=\tau$. Then for every $\tau\in[0,t)$
--
--   $$I_{2K}(\tau)\,a'(0)+\nu\int_0^\tau I_{2K}(\tau-s)\,g(s)\,ds\le a(\tau)-a(0).\tag{2.30}$$
--
--   The paper obtains it from (2.27) with $\zeta(s)=I_{2K}(\tau-s)$. With $a=\mathsf A_t[f;\varphi]$ it yields the reverse Poincaré-type estimate (2.34) of Corollary 2.3 (iv).
--
--   **Formalization Note** $a'(0)$ is the right derivative, given as the value at $0$ of the derivative witness of $a\in C^1([0,t))$.
-- source:
--   arXiv:1209.5786v4, (2.30), p. 18 (with (2.27), (2.29), p. 17)

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Gamma_Calculus

namespace BERicci.Gamma

open MeasureTheory Topology
open scoped ENNReal

/-- (2.30), p. 18: under Lemma 2.2 (i), `I_{2K}(τ) a'(0) + ν ∫₀^τ I_{2K}(τ − s) g(s) ds ≤ a(τ) − a(0)`
for every `τ ∈ [0,t)`. -/
theorem eq_2_30 (K ν t : ℝ) (ht : 0 < t) (hν : 0 ≤ ν)
    (a ap g : ℝ → ℝ) (ha : IsC1Ico t a ap) (hg : ContinuousOn g (Set.Ico 0 t))
    (h : L22Cond1 K ν t a ap g) :
    ∀ τ ∈ Set.Ico 0 t,
      IK (2 * K) τ * ap 0 + ν * ∫ s in (0 : ℝ)..τ, IK (2 * K) (τ - s) * g s
        ≤ a τ - a 0 := by sorry

end BERicci.Gamma
