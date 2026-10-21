-- Prove2me | Theorems.Thm_BrandLicensing_Intensive_eq_13_royalty
-- name    : BrandLicensing.Intensive.eq_13_royalty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:22.65253+00:00
-- url     : https://prove2.me/theorems/643cc096-eff1-4f5a-811f-ef0ed9f50e5e
-- title:
--   Eq. (13), p. 3188 — the brand owner's optimal royalty s = ½(1 − α)(e_C − λμ)
-- statement:
--   Under the standing assumptions with $\rho>0$ and $\alpha<1$, let the licensee respond to $(e_C,s)$ by its effort (12), $e_E(e_C,s)=\frac{\rho}{2-\rho}\max\{(1-\alpha)e_C-s,0\}$. For a core effort $e_C>0$ with $\lambda\mu\le e_C$, a royalty $s\ge0$ maximizes the brand owner's licensing profit (14) evaluated at $e_E(e_C,s)$, over all $s\ge0$, if and only if
--   $$s=\tfrac12(1-\alpha)(e_C-\lambda\mu).$$
--
--   The optimal royalty trades licensing revenue against the licensee's effort, which raises the brand owner's core revenue through the reciprocal effect; it decreases in $\lambda$, $\mu$ and $\alpha$.
--
--   **Formalization Note** Two hypotheses are added to the page's sentence. $\lambda\mu\le e_C$: for $e_C<\lambda\mu$ the formula is negative and the constraint $s\ge0$ binds (the optimum is $s=0$). $\rho>0$, $\alpha<1$ and $e_C>0$: otherwise the royalty does not affect the brand owner's profit and the maximizer is not unique. In the licensing equilibrium $e^L_C\ge\mu\ge\lambda\mu$, so (13) applies there.
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), p. 3188 (PDF 8), §4.2.2.2, eq. (13)

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

namespace BrandLicensing.Intensive

/-- (13), p. 3188: when the licensee responds by (12), the brand owner's optimal royalty for a core
effort `c > 0` with `λμ ≤ c` is unique and equals `½(1 − α)(c − λμ)`. -/
theorem eq_13_royalty (P : Params) (hP : P.Standing) (hρ : 0 < P.ρ) (hα : P.α < 1)
    (c : ℝ) (hc : 0 < c) (hcl : P.lam * P.μ ≤ c) (s : ℝ) (hs : 0 ≤ s) :
    (∀ s', 0 ≤ s' → piOwnerLic P c s' (eE12 P c s') ≤ piOwnerLic P c s (eE12 P c s)) ↔
      s = s13 P c := by sorry
end BrandLicensing.Intensive
