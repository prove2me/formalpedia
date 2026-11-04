-- Prove2me | Theorems.Thm_AIMInventory_UnknownRho_claim_14
-- name    : AIMInventory.UnknownRho.claim_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:30.957982+00:00
-- url     : https://prove2.me/theorems/dbd46f24-fbea-4b28-8b0f-fe2a2462797a
-- title:
--   Claim (14) — (h/T) E[Σ_{t=K̃+1}^T Z_t(m)] ≤ 2hm E[|J₁(ρ′)|²]/√T
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. nonnegative demands with finite positive mean, fix the non-perishable AIM parameters $\gamma,\bar y,h,b>0$ and put $m=h\gamma\bar y/\max\{b,h\}$. Let $Z_t(m)$ be the queue $Z_1(m)=0$, $Z_{t+1}(m)=[Z_t(m)+m/\sqrt t-D_t]^+$, let $\tilde T=\lceil(m/\rho')^2\rceil$ and $\tilde K=\min\{t>\tilde T:Z_t(m)=0\}$ (possibly $\infty$), and let $|J_1(\rho')|$ be the length of the first busy period of the fixed-inflow queue $W_1(\rho')=0$, $W_{t+1}(\rho')=[W_t(\rho')+\rho'-D_t]^+$, i.e. $|J_1(\rho')|=\inf\{t>1:W_t(\rho')=0\}-1$.
--
--   If $0<\rho'<\min\{m,E[D_1]\}$, then for every $T\ge1$
--   $$\frac hT\,E\Big[\sum_{t=\tilde K+1}^{T}Z_t(m)\Big]\le\frac{2hm\,E\big[|J_1(\rho')|^2\big]}{\sqrt T}. \tag{14}$$
--
--   Once the queue $Z(m)$ has emptied after $\tilde T$, it is dominated by the stationary-increment queue with inflow $\rho'$, and the claim bounds the cost of the remaining periods by the second moment of a busy period. Together with the bound on $E[\tilde K]$ it gives Theorem 8.
--
--   **Formalization Note.** The paper writes $\sum_{t=\tilde K+1}^T E[Z_t(m)]$ with the random index $\tilde K$ outside the expectation; as in (13) and Appendix E, the Lean statement reads it as $E\big[\sum_{t=1}^T \mathbf 1[\tilde K<t]\,Z_t(m)\big]$. The sum is empty when $\tilde K\ge T$ or $\tilde K=\infty$. Both sides are in $[0,\infty]$, so an infinite $E[|J_1(\rho')|^2]$ makes the bound trivial rather than junk. The hypothesis $\rho'>0$ is implicit in the paper.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 14, proof of Theorem 8, Eq. (14); proved in Appendix E, pp. 20–21

import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace AIMInventory.UnknownRho

/-- Claim (14), p. 14, with the random lower summation limit inside the
expectation, as required by (13) and Appendix E. -/
theorem claim_14 (P : DemandLaw) (c : Parameters) (ρ' : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (hρ : 0 < ρ') (hsmall : ρ' < m c)
    (hmean : ρ' < CappedBaseStock.mean P) :
    ENNReal.ofReal (c.h / (T : ℝ)) *
      (∫⁻ d, ∑ t ∈ Finset.Icc 1 T,
        if restartTime c ρ' d < (t : ℝ≥0∞) then
          ENNReal.ofReal (Z d (m c) t) else 0
        ∂CappedBaseStock.demandPathLaw P) ≤
      ENNReal.ofReal (2 * c.h * m c / Real.sqrt (T : ℝ)) *
        busySecondMoment P ρ' := by sorry

end AIMInventory.UnknownRho
