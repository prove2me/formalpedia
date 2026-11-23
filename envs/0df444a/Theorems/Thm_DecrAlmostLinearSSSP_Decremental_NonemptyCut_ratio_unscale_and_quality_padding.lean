-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_ratio_unscale_and_quality_padding
-- name    : DecrAlmostLinearSSSP.Decremental.NonemptyCut.ratio_unscale_and_quality_padding
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:56.578999+00:00
-- url     : https://prove2.me/theorems/dc3622bc-1678-4bee-a4c7-7dbc5dec2740
-- title:
--   Unscaling a ratio cut and padding its quality factor
-- statement:
--   Fix $S>0$ and scale all capacities of a physical instance $g$ to $\widehat u_e=Su_e$. Suppose a cut $C$ and numbers $G,U$ satisfy the dynamic minimum-ratio guarantee for $\widehat u$ with quality $K_0>0$ and capacity envelope $SU$. Then the same $C,G,U$ satisfy the guarantee for the original capacities with any quality denominator $K\ge K_0$:
--
--   $$
--   G=\gamma(C)<0,\qquad 0<U,\qquad \operatorname{cut}_u(C)\le U,
--   $$
--
--   and, whenever $\|x\|_u>0$,
--
--   $$
--   \frac{G}{U}\le \frac{\gamma\cdot x}{K\|x\|_u}.
--   $$
--
--   Indeed, $\|x\|_{\widehat u}=S\|x\|_u$ and $\operatorname{cut}_{\widehat u}(C)=S\operatorname{cut}_u(C)$, so all factors $S$ cancel. Increasing the denominator only weakens the negative-direction ratio requirement; nonnegative directions are immediate from $G/U<0$. Taking $K=\max\{32,K_0\}$ gives the quality padding needed by the public dynamic-cut interface.
--
--   **Formalization Note** The scaled graph is a record update of the existing `Physical` type, and the conclusion uses the existing `RatioGuarantee`; no auxiliary definition is required.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p. 9, Lemma 3.2 and equation (3.12), with the $K\ge32$ initialization convention on p. 10; capacity unscaling and quality padding for the polynomial numerical-range wrapper; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf.

import Definitions.Def_DecrAlmostLinearSSSP_NonemptyCutProtocol

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

/-- Unscale a ratio tuple and weaken its positive approximation denominator. -/
theorem DecrAlmostLinearSSSP.Decremental.NonemptyCut.ratio_unscale_and_quality_padding
    {n k : ℕ} {S G U K₀ K : ℝ}
    (g : Physical n k) (C : Finset (Fin n)) (hS : 0 < S)
    (hK₀ : 0 < K₀) (hKK : K₀ ≤ K)
    (h : RatioGuarantee { g with u := fun e => S * g.u e } K₀ G (S * U) C) :
    RatioGuarantee g K G U C := by sorry
