-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_proposition_2
-- name    : DataTrackComp.Surplus.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:42.07497+00:00
-- url     : https://prove2.me/theorems/6342efe2-be0a-41ff-9882-2a7253758ef8
-- title:
--   Proposition 2, p. 17 — myopic setting: equilibrium exists; prices (3.1); threshold path; firm A's demand equals p^{A,M}_1 < 1/2
-- statement:
--   Let $\bar u>0$ and $m>0$. In the myopic setting (data tracking, consumer maximizes product-1 utility only), an equilibrium exists. Every equilibrium has the following path.
--
--   1. Product-1 prices are
--   $$p^{A,M}_1=\max\{1/2-m/12,\,0\},\qquad p^{B,M}_1=\max\{1/2-m/6,\,-1/2\}.\qquad(3.1)$$
--   2. A type $(s,\theta)$ of the square with $s>p^{B,M}_1-p^{A,M}_1+1/2$ buys product 1 from firm B. Firm B then charges $m\theta$ for product 2 (for $\theta>0$).
--   3. A type with $s<p^{B,M}_1-p^{A,M}_1+1/2$ buys product 1 from firm A. When this set of types is nonempty, firm B charges the untracked consumer $p^{B,M}_2=m/2$.
--   4. Firm B's expected product-1 demand exceeds firm A's, and firm A's expected demand equals $p^{A,M}_1<1/2$.
--
--   These are the myopic-setting prices and path used in Claim 20 to compute $CS^M$.
--
--   **Formalization Note.** The untracked price is pinned only when $p^{B,M}_1-p^{A,M}_1+1/2>0$; otherwise the untracked information set is reached with probability zero. The tracked price is pinned for $\theta>0$ (at $\theta=0$ every nonnegative price is optimal).
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. 17 (PDF 17), Proposition 2, (3.1)

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
open MeasureTheory

namespace DataTrackComp.Surplus

theorem proposition_2 (ubar m : ℝ) (hu : 0 < ubar) (hm : 0 < m) :
    (∃ E : Assessment, IsEquilibrium .myopic ubar m E) ∧
    ∀ E : Assessment, IsEquilibrium .myopic ubar m E →
      E.pA = max (1 / 2 - m / 12) 0 ∧ E.pB = max (1 / 2 - m / 6) (-1 / 2) ∧
      (∀ τ ∈ square, (E.pB - E.pA + 1 / 2 < τ.1 → (E.cont E.pA E.pB).γ1 τ = 1) ∧
        (τ.1 < E.pB - E.pA + 1 / 2 → (E.cont E.pA E.pB).γ1 τ = 0)) ∧
      (∀ τ ∈ square, 0 < τ.2 → (E.cont E.pA E.pB).pT τ = m * τ.2) ∧
      (0 < E.pB - E.pA + 1 / 2 → (E.cont E.pA E.pB).pU = m / 2) ∧
      (∫ τ, (1 - (E.cont E.pA E.pB).γ1 τ) ∂μ0 < ∫ τ, (E.cont E.pA E.pB).γ1 τ ∂μ0 ∧
        ∫ τ, (1 - (E.cont E.pA E.pB).γ1 τ) ∂μ0 = E.pA ∧ E.pA < 1 / 2) := by sorry

end DataTrackComp.Surplus
