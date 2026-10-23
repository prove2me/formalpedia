-- Prove2me | Theorems.Thm_ContingentSourcing_Competition_lemma_A_1
-- name    : ContingentSourcing.Competition.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:01.115079+00:00
-- url     : https://prove2.me/theorems/895a27ea-fae8-4df5-969c-8316a0ea830c
-- title:
--   Lemma A.1, OA p. 1 (PDF 33) — with perfect shipment information, supplier R's best response to w_U in four regimes
-- statement:
--   Take perfect shipment information, $\rho=1$, and a price $w_U$ of supplier U with $c_U/P_1\le w_U\le m$. A pair $(w_R,w_E)$ with $c_R\le w_R\le w_E\le m$ is a best response of supplier R if it maximizes R's payoff (5) given $w_U$. Supplier R's best responses are as follows.
--
--   1. If $w_U>(m+c_R)/2$, the best responses are exactly $w_R=(m+c_R)/2$ with any $w_E\in[(m+c_R)/2,m]$.
--   2. If $\frac{P_0m+c_R}{P_0+1}<w_U\le\frac{m+c_R}{2}$, the best responses are exactly $w_R=w_U$ with any $w_E\in[w_U,m]$.
--   3. If $c_R<w_U\le\frac{P_0m+c_R}{P_0+1}$, then
--   $$w_R^*=\frac{P_1w_U+P_0m+c_R}{2}$$
--   with any $w_E\le m$ satisfying $w_E>(w_R^*-P_1w_U)/P_0$ is a best response; when $w_U<\frac{P_0m+c_R}{P_0+1}$ these are all the best responses.
--   4. If $w_U\le c_R$, then $w_E=(m+c_R)/2$ with any $w_R$ satisfying $\max(c_R,P_0w_E+P_1w_U)\le w_R\le w_E$ is a best response; when $w_U<c_R$ these are all the best responses.
--
--   In regimes 1–2 R takes the whole initial order, in regime 3 a part of it, and in regime 4 only the emergency order. These best responses are one half of the graphical construction of the equilibria of Proposition 2.
--
--   **Formalization Note.** The lemma is stated as a characterization: the listed pairs are best responses, and every best response has the listed form. The second half is dropped at the two regime endpoints $w_U=\frac{P_0m+c_R}{P_0+1}$ and $w_U=c_R$, where it is false as printed: there the best response of the neighbouring regime earns the same payoff (at $w_U=c_R$, the diversification price $(P_1c_R+P_0m+c_R)/2$ and the emergency-only response both give $P_0(m-c_R)^2/8$; at $w_U=\frac{P_0m+c_R}{P_0+1}$, $w_R^*=w_U$ and any $w_E\in[w_U,m]$ is a best response). "Any $w_E^*\ge w_R^*$" is read within the strategy space ($w_E\le m$). The printed "at time 1" in regimes 1–3 refers to the initial order (Time 0); this does not enter the statement, which is about prices only.
-- source:
--   Lu & Tomlin, Forewarned Is Forearmed?, SSRN 4260604 author manuscript (1 May 2023) of MSOM doi:10.1287/msom.2021.0540, Online Appendix p. 1 (PDF 33), Lemma A.1

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

namespace ContingentSourcing.Competition

/-- Lemma A.1, OA p. 1: with ρ = 1, supplier R's best responses to w_U in the four regimes. In each regime
the listed price pairs are best responses (w_E ranges up to the strategy-space bound m), and every best
response has that form, except at the two regime endpoints w_U = (P0 m + cR)/(P0 + 1) and w_U = cR,
where a best response of the neighbouring regime ties and the printed set is not exhaustive. -/
theorem lemma_A_1 (P : Params) (hP : P.Standing) (wU : ℝ) (hwU : P.UFeasible wU) :
    ((P.m + P.cR) / 2 < wU →
      (∀ wE, (P.m + P.cR) / 2 ≤ wE → wE ≤ P.m →
        P.IsBestResponseR 1 wU ((P.m + P.cR) / 2) wE) ∧
      (∀ wR wE, P.IsBestResponseR 1 wU wR wE → wR = (P.m + P.cR) / 2)) ∧
    ((P.P0 * P.m + P.cR) / (P.P0 + 1) < wU → wU ≤ (P.m + P.cR) / 2 →
      (∀ wE, wU ≤ wE → wE ≤ P.m → P.IsBestResponseR 1 wU wU wE) ∧
      (∀ wR wE, P.IsBestResponseR 1 wU wR wE → wR = wU)) ∧
    (P.cR < wU → wU ≤ (P.P0 * P.m + P.cR) / (P.P0 + 1) →
      (∀ wE, ((P.P1 * wU + P.P0 * P.m + P.cR) / 2 - P.P1 * wU) / P.P0 < wE → wE ≤ P.m →
        P.IsBestResponseR 1 wU ((P.P1 * wU + P.P0 * P.m + P.cR) / 2) wE) ∧
      (wU < (P.P0 * P.m + P.cR) / (P.P0 + 1) → ∀ wR wE, P.IsBestResponseR 1 wU wR wE →
        wR = (P.P1 * wU + P.P0 * P.m + P.cR) / 2 ∧ (wR - P.P1 * wU) / P.P0 < wE)) ∧
    (wU ≤ P.cR →
      (∀ wR, P.P0 * ((P.m + P.cR) / 2) + P.P1 * wU ≤ wR → P.cR ≤ wR →
        wR ≤ (P.m + P.cR) / 2 → P.IsBestResponseR 1 wU wR ((P.m + P.cR) / 2)) ∧
      (wU < P.cR → ∀ wR wE, P.IsBestResponseR 1 wU wR wE →
        wE = (P.m + P.cR) / 2 ∧ P.P0 * wE + P.P1 * wU ≤ wR)) := by sorry

end ContingentSourcing.Competition
