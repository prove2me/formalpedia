-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_lemma_5_discount_invariance
-- name    : FVRPricing.DecayBalancing.lemma_5_discount_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:57.821262+00:00
-- url     : https://prove2.me/theorems/58f1b1cc-ac01-469e-87d4-290e79b098e5
-- title:
--   Lemma 5 — invariance of the value function under rescaling the discount rate
-- statement:
--   Let $f$ satisfy Assumption 1, let $\pi$ be a policy, $\alpha>0$, and define $\pi'(x,a,b) = \pi(x,a,b/\alpha)$. Write $J^{\pi,\alpha}$ for the value of $\pi$ at discount rate $\alpha$. Then for every state $z = (x,a,b)$ with $a,b>0$,
--   $$J^{\pi,\alpha}(z) = J^{\pi',1}(x,a,\alpha b),\qquad\text{and in particular}\qquad J^{*,\alpha}(z) = J^{*,1}(x,a,\alpha b).$$
--
--   This licenses the normalization $\alpha = e^{-1}$ of §6: a performance bound proved for one discount rate transfers to every other.
--
--   **Formalization Note** $b$ is the rate of the Gamma prior (mean $a/b$), so rescaling time by $\alpha$ replaces $b$ by $\alpha b$.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 18, Lemma 5

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem lemma_5_discount_invariance (f : ℝ → ℝ) (h1 : Assumption1 f)
    (π : ℕ → ℝ → ℝ → ℝ) (hπ : IsPolicy π) (α : ℝ) (hα : 0 < α) (x : ℕ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    Jpi f α π x a b = Jpi f 1 (fun x a b => π x a (b / α)) x a (α * b) ∧
    Jstar f α x a b = Jstar f 1 x a (α * b) := by sorry

end FVRPricing.DecayBalancing
