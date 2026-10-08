-- Prove2me | Theorems.Thm_AffinePolicyOpt_OneDim_property_P3
-- name    : AffinePolicyOpt.OneDim.property_P3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:07:39.191997+00:00
-- url     : https://prove2.me/theorems/a98f14cb-cc46-4484-ac01-52dd91792c37
-- title:
--   Property P3, p. 4 — u*(s) − u*(t) = −f·(s − t) for some f ∈ [0, 1], for the clamped optimal control law
-- statement:
--   Let $L\le U$ and $y^*$ be real numbers, and let $u^*(\theta)=\max\big(L,\min(U,\,y^*-\theta)\big)$ be the clamped control law. For any $s\le t$ there is $f\in[0,1]$ with
--   $$u^*(s)-u^*(t)=-f\,(s-t).$$
--
--   In words, the optimal control law is non-increasing and 1-Lipschitz. The paper uses this to show that the coefficients of the affine controller of Algorithm 1 obtained by matching satisfy $-b_i\le q_i\le 0$ (proof of Lemma 4.4).
--
--   **Formalization Note** The page states P3 for "two distinct arguments $s\le t$"; the Lean statement also allows $s=t$, where any $f$ works. The law is stated directly as the clamp, which is the optimal control law of Lemma 7.1.
-- source:
--   Bertsimas, Iancu & Parrilo, Optimality of Affine Policies in Multi-stage Robust Optimization, arXiv:0904.3986v1, p. 4, property P3

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Zonogon

namespace AffinePolicyOpt.OneDim

/-- Property P3: for the clamped control law `u*(θ) = max(L, min(U, y* − θ))` with `L ≤ U` and
any `s ≤ t`, `u*(s) − u*(t) = −f · (s − t)` for some `f ∈ [0, 1]`. -/
theorem property_P3 (L U ystar : ℝ) (hLU : L ≤ U) (s t : ℝ) (hst : s ≤ t) :
    ∃ f ∈ Set.Icc (0 : ℝ) 1,
      clampLaw L U ystar s - clampLaw L U ystar t = -f * (s - t) := by sorry

end AffinePolicyOpt.OneDim
