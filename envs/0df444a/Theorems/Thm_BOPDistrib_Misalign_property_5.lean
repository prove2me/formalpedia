-- Prove2me | Theorems.Thm_BOPDistrib_Misalign_property_5
-- name    : BOPDistrib.Misalign.property_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:27.311398+00:00
-- url     : https://prove2.me/theorems/cf4a6e1d-d7bc-4836-94ab-7e9fb65da46e
-- title:
--   Property 5 (second statement), pp. 41, 44 (PDF 42, 45) — MR dominates FR above m^MR and M above m̄^MR
-- statement:
--   Assume the standing assumptions and $w\le\bar w=\beta v_h+(1-\beta)y$ and $c_\theta\le\bar c_\theta=(1-\beta)(w-y)$. Then:
--   1. $m^F\le m^{MR}\le v_h$ and $m^F\le\bar m^{MR}\le v_h$;
--   2. if $m\ge m^{MR}$, then $\Pi^{MR}_D(\alpha)\ge\Pi^{FR}_D(\alpha)$ for every $\alpha>0$;
--   3. if $m\ge\bar m^{MR}$, then $\Pi^{MR}_D(\alpha)\ge\Pi^M_D$ for every $\alpha>0$.
--
--   Here
--   $$m^{MR}=v_h-\frac{(1-\beta)(w-y)-c_\theta}{(1-\gamma)\beta},\qquad \bar m^{MR}=v_h-\frac{\beta v_h+(1-\beta)y-w}{(1-\gamma)\beta}.$$
--   In the paper's terms, $a_1(m)=0$ for $m\ge m^{MR}$ and $a_2(m)=\infty$ for $m\ge\bar m^{MR}$. Above both thresholds the education-first strategy with returns is optimal for every risk aversion.
--
--   **Formalization Note** The page also lists $w\le m^F$, which fails for $\gamma>0$ (e.g. $\gamma=0.54$, $w=1.78$ give $m^F<0$); it is omitted. The proof's claim that $m\ge m^{MR}$ alone makes MR dominate F is also false before $\bar m^{MR}$: at $v_h=8$, $\beta=1/3$, $w=22/5$, $y=3$, $\gamma=1/2$, $\theta_0=9/10$, $c_\theta=3/5$, $b=1/125$, $m=6$, $\alpha=30$, one has $m=m^{MR}<\bar m^{MR}$ but $\Pi^F>\Pi^{MR}$. The auxiliary functions $a_1,a_2$ are not formalized: their boundary values are stated directly as dominance for all $\alpha>0$.
-- source:
--   Calmon, Jue-Rajasingh, Romero & Stenson, Operational strategies for distributing durable goods in the base of the pyramid, accepted manuscript (M&SOM 24(4), 2022; TSpace, SSRN 2882402), p. 41 (PDF 42), Property 5; p. 44 (PDF 45), proof of Property 5

import Mathlib
import Definitions.Def_BOPDistrib_Misalign_Model

namespace BOPDistrib.Misalign

/-- Property 5, second statement (p. 41, proof p. 44): if `w ≤ w̄` and `cθ ≤ c̄θ`, then
`m^F ≤ m^MR, m̄^MR ≤ v_h`; MR dominates FR for every `α > 0` once `m ≥ m^MR`; and MR dominates M
for every `α > 0` once `m ≥ m̄^MR`. -/
theorem property_5 (P : Params) (m : ℝ) (hS : Standing P m) (hw : P.w ≤ wbar P)
    (hc : P.cθ ≤ cθbar P) :
    (mF P ≤ mMR P ∧ mF P ≤ mMRbar P ∧ mMR P ≤ P.vh ∧ mMRbar P ≤ P.vh) ∧
      (mMR P ≤ m → ∀ α : ℝ, 0 < α → PiFR P m α ≤ PiMR P m α) ∧
      (mMRbar P ≤ m → ∀ α : ℝ, 0 < α → PiM P m ≤ PiMR P m α) := by sorry

end BOPDistrib.Misalign
