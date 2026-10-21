-- Prove2me | Theorems.Thm_CurbEmissions_ExactStandard_lemma_1
-- name    : CurbEmissions.ExactStandard.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:13.747164+00:00
-- url     : https://prove2.me/theorems/ac799308-8a15-40da-b280-d12bc31555a2
-- title:
--   Lemma 1, p. 12 — the firm offers U iff s1 ≤ τ_U, D iff τ_U ≤ s1 ≤ τ_S, S iff s1 ≥ τ_S
-- statement:
--   Let the standing assumptions hold, let $R_1$'s standard be $s_1\ge0$ and $R_2$'s be $0$. Write
--   $$\tau_U=\frac{1}{c-\gamma}\Big(\bar u-\sqrt{\bar u^2-\frac{4\bar ur}{m_2}}\Big),\qquad \tau_S=\frac{1}{c-\gamma}\Big(\bar u-2\sqrt{\frac{\bar ur}{m_1}}\Big).$$
--   Then
--   1. the unified product (strategy $U$) is a profit-maximizing strategy of the firm if and only if $s_1\le\tau_U$;
--   2. differentiated products (strategy $D$) are profit-maximizing if and only if $\tau_U\le s_1\le\tau_S$;
--   3. serving only $M_2$ (strategy $S$) is profit-maximizing if and only if $s_1\ge\tau_S$.
--
--   The lemma describes the firm's reaction to $R_1$'s standard, which $R_1$ anticipates when choosing $s_1$.
--
--   **Formalization Note** "The firm offers $X$" is read as "$X$ is a best response", so at $s_1=\tau_U$ and $s_1=\tau_S$ two strategies are best responses at once; the paper fixes no tie-break.
-- source:
--   Han, Hu & Dawande, Curbing Emissions: Environmental Regulations and Product Offerings Across Markets, MSOM (authors' accepted manuscript, 2022-07-28), p. 12, Lemma 1

import Mathlib
import Definitions.Def_CurbEmissions_ExactStandard_Model

namespace CurbEmissions.ExactStandard

/-- Lemma 1, p. 12: given standard `s1 ≥ 0` in M1 and `0` in M2, strategy U is profit-maximizing iff
`s1 ≤ τ_U`, D iff `τ_U ≤ s1 ≤ τ_S`, and S iff `s1 ≥ τ_S`. -/
theorem lemma_1 (P : Params) (hP : Standing P) (s1 : ℝ) (hs1 : 0 ≤ s1) :
    (IsFirmBR P s1 .U ↔ s1 ≤ tauU P) ∧
    (IsFirmBR P s1 .D ↔ tauU P ≤ s1 ∧ s1 ≤ tauS P) ∧
    (IsFirmBR P s1 .S ↔ tauS P ≤ s1) := by sorry

end CurbEmissions.ExactStandard
