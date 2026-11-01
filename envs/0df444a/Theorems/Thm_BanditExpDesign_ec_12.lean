-- Prove2me | Theorems.Thm_BanditExpDesign_ec_12
-- name    : BanditExpDesign.ec_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:31.762538+00:00
-- url     : https://prove2.me/theorems/94d68bfd-d554-4203-8567-655bbcd409e0
-- title:
--   (EC.12) — the Bernstein variance bound $\bar V_t=(2+2C')^2(t+1)^{1+\alpha}\log(2/\delta)/(e-2)$
-- statement:
--   For $K\ge2$, $t\ge1$, $\alpha\in[0,1]$, $\delta\in(0,2/e)$ and $C'=K^2(1+e^2)$,
--   $$(2C'+1)(t+1)^{1+\alpha}\vee\frac{(2+2C')^2\vee(2+2Kt^\alpha)^2}{e-2}\log\frac2\delta\le(2C'+1)(t+1)^{1+\alpha}\vee\frac{(2+2C')^2\vee(4+4K)^2(t+1)^{1+\alpha}}{e-2}\log\frac2\delta\le\frac{(2+2C')^2(t+1)^{1+\alpha}}{e-2}\log\frac2\delta.$$
--
--   This real inequality brings the variance proxy and the increment bound under one deterministic sequence, the variance bound fed to Bernstein's inequality.
--
--   Differences from the source:
--   - reading: the chain V_t^{(i,j)} ≤ line 1 ≤ line 2 ≤ line 3 → line 1 ≤ line 2 and line 2 ≤ line 3; reason: the step V_t ≤ line 1 is the variance proxy bound, a separate item; what remains is a real inequality
--   - encoding: ∨; log → max; Real.log; reason: Lean conventions; same instances
-- source:
--   Simchi-Levi–Wang, Multi-armed Bandit Experimental Design, SSRN 4224969, proof of Theorem 7, eq. (EC.12), p.ec12

import Mathlib
import Definitions.Def_BanditExpDesign_EXP3EG

set_option autoImplicit false

namespace BanditExpDesign

/-- **(EC.12)**, Simchi-Levi–Wang, *Multi-armed Bandit Experimental Design*, SSRN 4224969, proof of
Theorem 7, p.ec12: the two inequalities of the chain
`(2C'+1)(t+1)^{1+α} ∨ [((2+2C')² ∨ (2+2Kt^α)²)/(e-2) · log(2/δ)]
≤ (2C'+1)(t+1)^{1+α} ∨ [((2+2C')² ∨ ((4+4K)²(t+1)^{1+α}))/(e-2) · log(2/δ)]
≤ (2+2C')²(t+1)^{1+α}/(e-2) · log(2/δ)`, with `C' = K²(1+e²)`.

**Formalization Note.** A real inequality with no bandit. `∨` is `max`; the logarithm is natural. -/
theorem ec_12 {K : ℕ} (hK : 2 ≤ K) {α δ : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hδ0 : 0 < δ) (hδ : δ < 2 / Real.exp 1) (t : ℕ) (ht : 1 ≤ t) :
    max ((2 * constC' K + 1) * ((t : ℝ) + 1) ^ (1 + α))
        (max ((2 + 2 * constC' K) ^ 2) ((2 + 2 * (K : ℝ) * (t : ℝ) ^ α) ^ 2) / (Real.exp 1 - 2) *
          Real.log (2 / δ)) ≤
      max ((2 * constC' K + 1) * ((t : ℝ) + 1) ^ (1 + α))
        (max ((2 + 2 * constC' K) ^ 2) ((4 + 4 * (K : ℝ)) ^ 2 * ((t : ℝ) + 1) ^ (1 + α)) /
          (Real.exp 1 - 2) * Real.log (2 / δ)) ∧
    max ((2 * constC' K + 1) * ((t : ℝ) + 1) ^ (1 + α))
        (max ((2 + 2 * constC' K) ^ 2) ((4 + 4 * (K : ℝ)) ^ 2 * ((t : ℝ) + 1) ^ (1 + α)) /
          (Real.exp 1 - 2) * Real.log (2 / δ)) ≤
      (2 + 2 * constC' K) ^ 2 * ((t : ℝ) + 1) ^ (1 + α) / (Real.exp 1 - 2) *
        Real.log (2 / δ) := by sorry

end BanditExpDesign
