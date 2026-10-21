-- Prove2me | Theorems.Thm_BrandLicensing_Intensive_eq_12_licensee_effort
-- name    : BrandLicensing.Intensive.eq_12_licensee_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:02.869633+00:00
-- url     : https://prove2.me/theorems/538afed0-9d93-4b05-beb5-4ea2620cd581
-- title:
--   Eq. (12), p. 3188 — the licensee's effort is ρ/(2 − ρ)·[(1 − α)e_C − s] if s < (1 − α)e_C, else 0
-- statement:
--   Under the standing assumptions, fix a core effort $e_C\ge0$ and a royalty $s\ge0$. An effort $e_E\ge0$ maximizes the licensee's profit $\pi_L=\rho\max\{(1-\alpha)e_C+e_E-s,0\}^2/4-\tfrac12e_E^2$ (10) over $e_E\ge0$ if and only if
--   $$e_E=\frac{\rho}{2-\rho}\max\{(1-\alpha)e_C-s,\;0\}.$$
--
--   So the licensee's best response is unique: it is the solution $\frac{\rho}{2-\rho}[(1-\alpha)e_C-s]$ of the first-order condition (11) when $s<(1-\alpha)e_C$, and $0$ otherwise. It does not depend on $\theta$ or $\lambda$, and it decreases in $s$ (double marginalization).
--
--   **Formalization Note** The case $s\ge(1-\alpha)e_C$ ("otherwise, $e_E$ vanishes") relies on the positive part in the definition of $\pi^M$.
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), p. 3188 (PDF 8), §4.2.2.1, eqs. (11), (12)

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

namespace BrandLicensing.Intensive

/-- (12), p. 3188: for every core effort `c ≥ 0` and royalty `s ≥ 0`, the licensee's optimal effort
is unique and equals `ρ/(2 − ρ)·[(1 − α)c − s]` if `s < (1 − α)c`, and `0` otherwise. -/
theorem eq_12_licensee_effort (P : Params) (hP : P.Standing) (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (e : ℝ) (he : 0 ≤ e) :
    (∀ e', 0 ≤ e' → piLicensee P c s e' ≤ piLicensee P c s e) ↔ e = eE12 P c s := by sorry
end BrandLicensing.Intensive
