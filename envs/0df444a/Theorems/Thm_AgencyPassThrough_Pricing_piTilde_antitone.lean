-- Prove2me | Theorems.Thm_AgencyPassThrough_Pricing_piTilde_antitone
-- name    : AgencyPassThrough.Pricing.piTilde_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:39.859527+00:00
-- url     : https://prove2.me/theorems/5fed336b-f8f1-4626-bb99-2967b39946fc
-- title:
--   Proof of Proposition 2(i) — declining auxiliary e-tailer profit
-- statement:
--   For demand satisfying the standing conditions, write $\tilde\pi(p)=\lambda(p)q(p)$. This curve is strictly decreasing throughout the price interval $D$. At any wholesale equilibrium price $p^W\in D$, the e-tailer's wholesale contract profit equals
--
--   $$\pi_r^W=n\lambda(p^W)q(p^W).$$
--
--   Together with the agency profit lower bound, this gives the e-tailer comparison when $p^B\leq p^W$.
--
--   **Formalization Note** The decreasing claim uses A1 and $\lambda'<1$; the profit equality unfolds the wholesale price from Lemma 1.
-- source:
--   Hu, Zheng & Pan, Agency or Wholesale? The Role of Retail Pass-Through, SSRN preprint 3724934 (2021 revision, PDF sha256 1ab91ed8…), p. 27, proof of Proposition 2(i), auxiliary profit derivative

import Mathlib
import Definitions.Def_AgencyPassThrough_Pricing_Model

namespace AgencyPassThrough.Pricing

/-- π̃ decreases; wholesale e-tailer profit identity, proof of Proposition 2(i), p. 27. -/
theorem piTilde_antitone (q : ℝ → ℝ) (D : Set ℝ)
    (hq : DemandStanding q D) (n : ℕ) (pW : ℝ) (hpW : pW ∈ D) :
    StrictAntiOn (piTilde q) D ∧
      piWr n q pW = (n : ℝ) * lam q pW * q pW := by sorry

end AgencyPassThrough.Pricing
