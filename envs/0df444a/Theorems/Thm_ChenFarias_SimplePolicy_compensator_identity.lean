-- Prove2me | Theorems.Thm_ChenFarias_SimplePolicy_compensator_identity
-- name    : ChenFarias.SimplePolicy.compensator_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:40.450557+00:00
-- url     : https://prove2.me/theorems/13a50471-250c-4efb-84b0-310d4ece0d44
-- title:
--   Proof of Lemma 8, p. 1131 — expected revenue equals integrated expected rate
-- statement:
--   Let $\lambda>0$, let $f$ be an admissible valuation density with tail $\bar F$, and let $\pi(x)\ge0$ for every positive inventory level. Start with $x_0\in\mathbb N$ items and construct sales with rate $\lambda\bar F(\pi(x))$ at inventory $x$.
--
--   For a nonnegative inventory price policy and every horizon $T\ge0$, expected revenue from sales by $T$ equals expected integrated revenue intensity:
--
--   $$J(x_0,T)=\mathbb E\!\left[\int_0^T \lambda\pi(X_{t-})\bar F(\pi(X_{t-}))\,dt\right].$$
--
--   It turns revenue counted at sale epochs into a time integral of the revenue rate. This is how Lemma 8 passes from the pathwise monotonicity of Lemma 7 to expectations.
--
--   **Formalization Note** The printed compensator omits $\lambda$; equation (2) supplies it. This item needs only positive $\lambda$, Assumption 1 and nonnegative prices at positive inventory; it does not assume that the policy solves the Bellman equation. The integral is over $(0,T]$, which has the same value as $[0,T]$.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1131, proof of Lemma 8, compensator display

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model

open MeasureTheory
open scoped ENNReal

namespace ChenFarias.SimplePolicy

/-- The expected-sales compensation identity used in the proof of Lemma 8.
The factor `lam` corrects the missing factor in the printed display. -/
theorem compensator_identity (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ)
    (x0 : ℕ) (T : ℝ) (hlam : 0 < lam) (hf : Assumption1 f)
    (hπ : ∀ x : ℕ, 1 ≤ x → 0 ≤ π x) (hT : 0 ≤ T) :
    J lam f π x0 T =
      ∫⁻ e, (∫⁻ t in Set.Ioc 0 T,
        ENNReal.ofReal (lam * rateRev f π (Xminus lam f π x0 e t)) ∂volume)
        ∂clockLaw x0 := by sorry

end ChenFarias.SimplePolicy
