-- Prove2me | Theorems.Thm_BrandLicensing_Intensive_proposition_3
-- name    : BrandLicensing.Intensive.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:13.630111+00:00
-- url     : https://prove2.me/theorems/a53261ab-b04e-4134-b751-ace1392f2361
-- title:
--   Proposition 3, p. 3189 (PDF 9) — at the intensive margin, licensing yields a higher-quality extension than in-house development, so brand dilution is less likely
-- statement:
--   Consider the brand-extension model under the standing assumptions $0\le\alpha\le1$, $\theta\ge1$, $\mu>0$, $0\le\rho<1$, $0\le\lambda\le1$, $\varepsilon>0$. Let $(e^H_C,e^H_E)$ be an in-house equilibrium (a maximizer of the in-house profit (7) over $e_C,e_E\ge0$) with profit $\pi^H_B$, and let $\sigma$ be a subgame-perfect equilibrium of the licensing game with royalty $s^L$, licensee effort $e^L_E$ and brand-owner profit $\pi^L_B$. Suppose the parameters lie on the **intensive margin**: the brand owner is indifferent between the two modes, and extending the brand is strictly better than not extending it,
--   $$\pi^H_B=\pi^L_B>\pi^{NE}_B,$$
--   where the last inequality means $\pi^H_B>\mu e_C-\tfrac12e_C^2$ for every core effort $e_C\ge0$. Then
--
--   1. a switch from in-house development to licensing increases the quality of the extension: $e^H_E<e^L_E$;
--   2. it therefore lowers the probability of brand dilution: for every probability law $\nu$ of the shock $\xi_E$ to the extension's perceived quality,
--   $$\nu\{\xi_E:\ e^L_E+\xi_E<\varepsilon\}\le\nu\{\xi_E:\ e^H_E+\xi_E<\varepsilon\},$$
--   and the inequality is strict whenever $\nu$ gives positive mass to every nonempty open interval.
--
--   This is the paper's key result: it runs against the received view that brand licensing causes brand dilution. Brand dilution means that the reciprocal effect $\lambda(1-\alpha)(e_E+\xi_E-\varepsilon)$ on the core product's value is negative.
--
--   **Formalization Note** The equilibria are taken as the optimizers of the model, not as the closed forms of Appendices A and B; the profits are evaluated at them. The no-extension profit is the maximum of $\mu e_C-\tfrac12e_C^2$, written as "exceeds every no-extension profit". The paper does not specify the law of the shock; the probability inequality is stated weakly for every law (a law that puts no mass between $\varepsilon-e^L_E$ and $\varepsilon-e^H_E$ gives equality) and strictly for every law of full support, which is the paper's "reduces". The shock $\xi_E$ follows §3.1; with risk-neutral firms it does not change the equilibrium.
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), p. 3189 (PDF 9), Proposition 3; intensive margin defined in §6, p. 3189 (PDF 9); proof in Appendix F, p. 3196 (PDF 16)

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

namespace BrandLicensing.Intensive

/-- Proposition 3, p. 3189: at the intensive margin (`π^H_B = π^L_B > π^NE_B`), a switch from in-house
development to licensing increases the quality of the extension, and therefore lowers the
probability of brand dilution `e_E + ξ_E < ε`: weakly under any law of the shock `ξ_E`, strictly
under every law that charges each nonempty open interval. -/
theorem proposition_3 (P : Params) (hP : P.Standing)
    (eCH eEH : ℝ) (hH : IsInHouseEq P eCH eEH)
    (σ : LicProfile) (hL : IsLicensingSPE P σ)
    (hI : piInHouse P eCH eEH = piOwnerLic P σ.eC σ.sL σ.eEL)
    (hNE : ∀ c, 0 ≤ c → piNoExt P c < piInHouse P eCH eEH) :
    eEH < σ.eEL ∧
    ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν],
      ν {ξ | σ.eEL + ξ < P.ε} ≤ ν {ξ | eEH + ξ < P.ε} ∧
      ((∀ x y : ℝ, x < y → 0 < ν (Set.Ioo x y)) →
        ν {ξ | σ.eEL + ξ < P.ε} < ν {ξ | eEH + ξ < P.ε}) := by sorry
end BrandLicensing.Intensive
