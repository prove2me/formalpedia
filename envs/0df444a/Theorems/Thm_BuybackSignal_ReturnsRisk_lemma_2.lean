-- Prove2me | Theorems.Thm_BuybackSignal_ReturnsRisk_lemma_2
-- name    : BuybackSignal.ReturnsRisk.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:57.077798+00:00
-- url     : https://prove2.me/theorems/53e6aa9a-a669-4cd4-a12a-1077f3d47ebc
-- title:
--   Lemma 2, p. 11 — the symmetric-information benchmark
-- statement:
--   For a known return-honoring probability $\theta\in(0,1]$, the feasible contract $(w^\circ,r^\circ(\theta))$ maximizes the manufacturer's profit over every $w\ge\theta r\ge0$. Its values are
--   $$
--   w^\circ=\frac{\alpha}{2\beta},\quad r^\circ(\theta)=\frac{\alpha_l}{2\beta\theta},\quad
--   \pi^\circ=\frac{\lambda^c\lambda(\Delta\alpha)^2+\alpha^2}{8\beta},\quad
--   s^\circ=\frac{\alpha_h}{4},\quad q^\circ=\frac{\Delta\alpha}{4}.
--   $$
--   The retailer orders $s^\circ$, has $q^\circ$ left after low demand, and nothing left after high demand. This is the benchmark for Proposition 1.
--
--   **Formalization Note** $\theta>0$ is explicit because the displayed returns price divides by $\theta$.
-- source:
--   Wang, Gurnani & Subramanian, The Informational Role of Buyback Contracts, SSRN 3166462 (author's revised version; Management Science 2020), p. 11 (PDF 11), Lemma 2 and problem (3)

import Mathlib
import Definitions.Def_BuybackSignal_ReturnsRisk_Model

namespace BuybackSignal.ReturnsRisk

theorem lemma_2 (P : Params) (hP : P.Standing)
    (θ : ℝ) (hθ : 0 < θ ∧ θ ≤ 1) :
    (P.w0, P.r0 θ) ∈ P.actionSet θ ∧
    P.Pi P.w0 (P.r0 θ) θ θ = P.pi0 ∧
    (∀ c : ℝ × ℝ, c ∈ P.actionSet θ →
      P.Pi c.1 c.2 θ θ ≤ P.Pi P.w0 (P.r0 θ) θ θ) ∧
    P.sR P.w0 (P.r0 θ) θ P.lam = P.s0 ∧
    P.unsoldLow P.w0 (P.r0 θ) θ P.lam = P.q0 ∧
    P.unsoldHigh P.s0 (P.r0 θ) θ = 0 := by sorry
end BuybackSignal.ReturnsRisk
