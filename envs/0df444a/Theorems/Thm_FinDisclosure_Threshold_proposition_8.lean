-- Prove2me | Theorems.Thm_FinDisclosure_Threshold_proposition_8
-- name    : FinDisclosure.Threshold.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:22.834222+00:00
-- url     : https://prove2.me/theorems/3edcdcf3-6c1c-473a-b1d9-9a68819a8349
-- title:
--   Proposition 8, p. 37 (first case) — if E_µ0 c < I, V* = ∫_ŝ^1 (s − c + B) µ0, attained by (17) with the binding ŝ (with λI ≤ B, I < c(1))
-- statement:
--   Assume the standing assumptions of the model, $\mathbb E_{\mu_0} c(s) < I$, $\lambda I \le B$ and $I < c(1)$. Then there is a threshold $\hat s \in (0,1)$ with
--   $$0 = \int_{\hat s}^1 \big(c(s) - I\big)\,\mu_0(s)\,ds,$$
--   and with $q = \int_{\hat s}^1 \mu_0(s)\,ds \in (0,1)$:
--
--   1. the threshold density (17) with $\hat S = [\hat s,1]$, $\mu_h = \mu_0/q$ on $[\hat s,1]$ and $0$ elsewhere, is feasible for (30);
--   2. its objective value is
--   $$V^* = \int_{\hat s}^1 \big(s - c(s) + B\big)\,\mu_0(s)\,ds; \tag{37}$$
--   3. $V^*$ is the maximum of the two-posterior problem (15): for every $q' \in (0,1)$ and every $\mu_h'$ feasible for (30) at $q'$,
--   $$q'\int_0^1 \big(s - c(s) + B + \lambda(c(s) - I)\big)\mu_h'(s)\,ds \le V^*.$$
--
--   The $\lambda$ term of the objective drops out of (37) because the financing constraint binds.
--
--   **Formalization Note** The paper's second case, "If $\mathbb E_{\mu_0} c(s) \ge I$, then no disclosure is optimal", is not formalized. Two hypotheses are added. $I < c(1)$ is what places $q$ in $(0,1)$, as in Lemma 6. $\lambda I \le B$ is needed because the proposition is false without it. With $\mu_0 = 1$, $c(s) = s$, $I = 0.6$, $B = 0.1$ and $\lambda = 1$, the binding threshold $\hat s = 0.2$ earns $0.08$, while the slack threshold $0.5$ earns $0.5\,(0.1 + 1\cdot(0.75 - 0.6)) = 0.125$. The maximum is stated as attained (`IsGreatest`), not as a supremum.
-- source:
--   Szydlowski, Optimal Financing and Disclosure, working paper (version of March 2017), pp. 37–38 (PDF 37–38), Proposition 8, eq. (37)

import Mathlib
import Definitions.Def_FinDisclosure_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace FinDisclosure.Threshold

/-- Proposition 8, pp. 37–38, first case (with the added hypotheses `λ I ≤ B` and `I < c(1)`): if
`E_{µ0} c(s) < I`, there is `ŝ ∈ (0, 1)` with `∫_ŝ^1 (c(s) - I) µ0(s) ds = 0`; with
`q = ∫_ŝ^1 µ0(s) ds ∈ (0, 1)`, the threshold density (17) with `Ŝ = [ŝ, 1]` is feasible for (30), and
its value `V* = ∫_ŝ^1 (s - c(s) + B) µ0(s) ds` (37) is the maximum of the two-posterior problem (15)
over all `q ∈ (0, 1)` and all feasible `µh`. -/
theorem proposition_8 (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hEc : ∫ s in (0:ℝ)..1, c s * f0 s < I) (hB : lam * I ≤ B) (hc1 : I < c 1) :
    ∃ shat : ℝ, 0 < shat ∧ shat < 1 ∧ ∫ s in shat..1, (c s - I) * f0 s = 0 ∧
      ∃ qbar : ℝ, qbar = ∫ s in shat..1, f0 s ∧ 0 < qbar ∧ qbar < 1 ∧
        Feas30 c f0 I qbar (thresholdDensity f0 qbar shat) ∧
        obj c I B lam qbar (thresholdDensity f0 qbar shat) = ∫ s in shat..1, (s - c s + B) * f0 s ∧
        IsGreatest {v : ℝ | ∃ q ∈ Ioo (0:ℝ) 1, ∃ m : ℝ → ℝ, Feas30 c f0 I q m ∧ v = obj c I B lam q m}
          (∫ s in shat..1, (s - c s + B) * f0 s) := by sorry

end FinDisclosure.Threshold
