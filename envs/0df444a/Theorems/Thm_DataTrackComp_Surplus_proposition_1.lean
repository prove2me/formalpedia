-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_proposition_1
-- name    : DataTrackComp.Surplus.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:43.997479+00:00
-- url     : https://prove2.me/theorems/894a0de9-47c9-4c05-acf0-d2a04a6c1c85
-- title:
--   Proposition 1, p. 16 — restricted setting: equilibrium exists; prices 1/2, 1/2; split at s = 1/2; product-2 price m/2
-- statement:
--   Let $\bar u>0$ and $m>0$. In the restricted setting (no data tracking), an equilibrium exists. Every equilibrium has the following path.
--
--   1. Both firms set product-1 price $1/2$.
--   2. A consumer of type $(s,\theta)$ in the square buys product 1 from firm A if $s<1/2$ and from firm B if $s>1/2$. The expected product-1 demand is $1/2$ for each firm.
--   3. Firm B sets product-2 price $p^{B,R}_2=m/2$.
--
--   This is the benchmark without tracking. The two markets decouple, so product 1 is a standard Hotelling duopoly and product 2 is a monopoly facing the prior.
--
--   **Formalization Note.** "Essentially unique" is stated as: every equilibrium has these prices, this product-2 price, and this choice at every type with $s\ne1/2$.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. 16 (PDF 16), Proposition 1

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
open MeasureTheory

namespace DataTrackComp.Surplus

theorem proposition_1 (ubar m : ℝ) (hu : 0 < ubar) (hm : 0 < m) :
    (∃ E : Assessment, IsEquilibrium .restricted ubar m E) ∧
    ∀ E : Assessment, IsEquilibrium .restricted ubar m E →
      E.pA = 1 / 2 ∧ E.pB = 1 / 2 ∧
      (∀ τ ∈ square, (τ.1 < 1 / 2 → (E.cont E.pA E.pB).γ1 τ = 0) ∧
        (1 / 2 < τ.1 → (E.cont E.pA E.pB).γ1 τ = 1)) ∧
      (∫ τ, (1 - (E.cont E.pA E.pB).γ1 τ) ∂μ0 = 1 / 2 ∧ ∫ τ, (E.cont E.pA E.pB).γ1 τ ∂μ0 = 1 / 2) ∧
      (E.cont E.pA E.pB).pU = m / 2 := by sorry

end DataTrackComp.Surplus
