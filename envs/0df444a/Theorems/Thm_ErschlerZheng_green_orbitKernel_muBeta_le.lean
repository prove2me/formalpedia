-- Prove2me | Theorems.Thm_ErschlerZheng_green_orbitKernel_muBeta_le
-- name    : ErschlerZheng.green_orbitKernel_muBeta_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T07:22:28.526977+00:00
-- url     : https://prove2.me/theorems/27983d31-af98-448f-bb97-12db4696b10f
-- title:
--   Proposition 7.11 — for k_n = A⌊log₂ n⌋ and every ε > 0, G_{P_{μ_β}}(x, y) ⩽ C (d/log₂^{2A} d)^{β−1} (log₂ d)^{−((1−β)/(1+β))(2A/D − ε)}
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $1 - \frac1D < \beta < 1$, let $A$ be a positive integer divisible by $D$, and let $\epsilon > 0$. Let $P$ be the transition kernel induced by $\mu_\beta$ (`muBeta`) with $k_n = A\lfloor\log_2 n\rfloor$ (`kLog A`) on the orbit $1^\infty \cdot G_\omega$ (`orbitKernel … oneRay`), and write $d = d_{\mathcal S}(x, y)$ for the Schreier distance (`orbitDist`). Then there is $C > 0$ such that for all $x, y$ in the orbit with $d \ge 2$, the Green function of $P$ (`MarkovChain.green`, valued in $[0, \infty]$) satisfies
--   $$\mathbf G_P(x, y) \le C \Bigl(\frac{d}{(\log_2 d)^{2A}}\Bigr)^{\beta-1} (\log_2 d)^{-\frac{1-\beta}{1+\beta}(\frac{2A}D - \epsilon)}.$$
--
--   Erschler and Zheng, p. 42, Proposition 7.11: “Let $\beta \in (1 - \frac1D, 1)$ and $k_n = A\lfloor\log_2 n\rfloor$. For any $\epsilon > 0$, there exists a constant $C = C(\beta, D, \epsilon) > 0$ such that for any $x, y \in 1^\infty \cdot G$, the Green function satisfies $\mathbf G_{P_{\mu_\beta}}(x, y) \leqslant C\bigl(\frac{d_{\mathcal S}(x,y)}{\log_2^{2A} d_{\mathcal S}(x,y)}\bigr)^{\beta-1}(\log_2 d_{\mathcal S}(x, y))^{-\frac{1-\beta}{1+\beta}(\frac{2A}D - \epsilon)}$.”
--
--   The bound is asserted for $d \ge 2$, where the printed right side is defined: at $d = 1$ it divides by $\log_2^{2A} 1 = 0$, and at $d = 0$ the logarithm is not defined. $\log_2^{2A} d$ is read as $(\log_2 d)^{2A}$. $A$ is a positive integer divisible by $D$, as in Proposition 7.18 and the choice of $k_n$ on p. 42. The constant is chosen after $\omega$ and $A$. These are standing parameters of §7: $\omega$ is fixed from §7.2 on (p. 35: “Throughout the rest of this section we assume that $\omega$ satisfies Assumption $(\mathrm{Fr}(D))$”), and $A$ is fixed with $k_n = A\lfloor\log_2 n\rfloor$ at the start of §7.3 (p. 42). The paper's $C = C(\beta, D, \epsilon)$ lists the parameters the proposition introduces, not a uniformity in $\omega$ and $A$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 42, Proposition 7.11

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
import Definitions.Def_MarkovChain_HeatKernels

namespace ErschlerZheng

theorem green_orbitKernel_muBeta_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    [DecidableEq (orbitOne ω)] (β : ℝ) (hβ1 : 1 - 1 / (D : ℝ) < β) (hβ2 : β < 1) (A : ℕ)
    (hA : 0 < A) (hDA : D ∣ A) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ x y : orbitOne ω, 2 ≤ orbitDist ω x y →
      MarkovChain.green (orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay) x y ≤
        ENNReal.ofReal (C *
          (orbitDist ω x y / Real.logb 2 (orbitDist ω x y) ^ (2 * A)) ^ (β - 1) *
          Real.logb 2 (orbitDist ω x y) ^ (-((1 - β) / (1 + β) * (2 * (A : ℝ) / D - ε)))) := by
  sorry

end ErschlerZheng
