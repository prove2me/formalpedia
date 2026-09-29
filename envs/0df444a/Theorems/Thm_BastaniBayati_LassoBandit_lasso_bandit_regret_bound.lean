-- Prove2me | Theorems.Thm_BastaniBayati_LassoBandit_lasso_bandit_regret_bound
-- name    : BastaniBayati.LassoBandit.lasso_bandit_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T09:27:08.949194+00:00
-- url     : https://prove2.me/theorems/a2a6d0c9-ceeb-4648-be20-80d1f038324d
-- title:
--   Regret bound of the LASSO Bandit (Bastani–Bayati, Theorem 1)
-- statement:
--   Work in Bastani and Bayati's high-dimensional covariate bandit: $K\ge2$ arms with parameters $\beta_i\in\mathbb R^d$, $d>2$; covariates $X_t$ i.i.d. from $\mathcal P_X$ on $\mathcal X\subseteq\mathbb R^d$; pulling arm $i$ at time $t$ yields $X_t^\top\beta_i+\varepsilon_{i,t}$ with independent $\sigma$-subgaussian noises ($\sigma>0$) independent of the covariates. Assume Assumptions 1–4 with constants $x_{\max}, b$ (parameter set), $C_0$ (margin), $h, p_*$ and the partition $\mathcal K_{opt}\cup\mathcal K_{sub}$ (arm optimality), and $\phi_0$ (compatibility); let $s_0$ be the sparsity parameter.
--
--   Run the LASSO Bandit with forced-sampling parameter $q\ge4\lceil q_0\rceil$, localization parameter $h$, and
--   $$\lambda_1=\frac{\phi_0^2p_*h}{64s_0x_{\max}},\qquad\lambda_{2,0}=\frac{\phi_0^2}{2s_0}\sqrt{\frac{1}{p_*C_1}}.$$
--   Then for every horizon $T\ge C_5$ its cumulative expected regret satisfies
--   $$R_T\le C_3(\log T)^2+\big[2Kbx_{\max}(6q+4)+C_3\log d\big]\log T+\big(2bx_{\max}C_5+2Kbx_{\max}+C_4\big),$$
--   with $C_1=C_1(\phi_0)$, $C_2=C_2(\phi_0)$, $C_3$, $C_4$, $C_5$, $q_0$ the explicit constants of the Constants definition (natural logarithms).
--
--   This is the main theorem of Bastani and Bayati: the regret grows like $(\log T)^2$ in the horizon and only logarithmically in the covariate dimension $d$, polynomially in the sparsity $s_0$.
--
--   **Formalization Note** Only the explicit inequality is stated, not the trailing $O(s_0^2[\log T+\log d]^2)$ or $q_0=O(s_0^2\log d)$. The page's "$t\ge C_5$" is the horizon condition $T\ge C_5$. The result is claimed for every LASSO selection rule and every tie-breaking rule of the arg max; both are required to be measurable so that the expectations in $R_T$ are genuine (a non-measurable integrand would have integral $0$ in Lean).
-- source:
--   Bastani & Bayati, Online Decision Making with High-Dimensional Covariates, Operations Research 68(1):276–294 (2020), doi:10.1287/opre.2019.1902, pp. 284–285, Theorem 1

import Mathlib
import Definitions.Def_BastaniBayati_LassoBandit_Basic
import Definitions.Def_BastaniBayati_LassoBandit_Model
import Definitions.Def_BastaniBayati_LassoBandit_Constants
import Definitions.Def_BastaniBayati_LassoBandit_Algorithm

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace BastaniBayati.LassoBandit

/-- **Theorem 1**, Bastani–Bayati, pp. 284–285. Under the model of §2.1 and Assumptions 1–4, when
`q ≥ 4⌈q₀⌉`, `K ≥ 2`, `d > 2`, `T ≥ C₅`, the LASSO Bandit run with the `h` of Assumption 3,
`λ₁ = φ₀²p_*h/(64s₀x_max)` and `λ₂,₀ = [φ₀²/(2s₀)]√(1/(p_*C₁))` — with any (measurable) LASSO
selection rule and any (measurable) arg-max tie-breaking rule — has cumulative expected regret
`R_T ≤ C₃(log T)² + [2Kbx_max(6q + 4) + C₃ log d] log T + (2bx_maxC₅ + 2Kbx_max + C₄)`. -/
theorem lasso_bandit_regret_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d K : ℕ}
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin K → ℕ → Ω → ℝ) (σ : ℝ≥0) (β : Fin K → Fin d → ℝ)
    (xmax b C0 h pstar φ0 : ℝ) (Kopt Ksub : Finset (Fin K)) (s0 : ℕ)
    (hmodel : IsCovariateNoiseModel P 𝒳 PX X ε σ) (hσ : 0 < σ)
    (hA1 : ParameterSet 𝒳 β xmax b) (hA2 : MarginCondition PX β C0)
    (hA3 : ArmOptimality 𝒳 PX β Kopt Ksub h pstar)
    (hA4 : CompatibilityAssumption 𝒳 PX β Kopt h φ0)
    (hs0 : s0 = sparsity β) (hK : 2 ≤ K) (hd : 2 < d)
    (sel : LassoSelector d) (hsel : IsLassoSelector sel)
    (hsel_meas : ∀ (n : ℕ) (lam : ℝ),
      Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => sel n p.1 p.2 lam))
    [NeZero K] (tb : ArgmaxRule K) (htb : IsArgmaxRule tb)
    (htb_meas : ∀ S : Finset (Fin K), Measurable (fun s : Fin K → ℝ => tb s S))
    (q T : ℕ)
    (hq : 4 * ⌈q0 d xmax h pstar (C1 s0 σ xmax φ0) (C2 s0 xmax φ0)⌉₊ ≤ q)
    (hT : C5 K q ≤ T) :
    cumRegret P X β
        (lassoBanditArm sel tb q h (lam1 s0 xmax h pstar φ0)
          (lam20 s0 pstar φ0 (C1 s0 σ xmax φ0)) X ε β) T ≤
      C3 K C0 xmax pstar (C1 s0 σ xmax φ0) * Real.log T ^ 2 +
        (2 * K * b * xmax * (6 * q + 4) + C3 K C0 xmax pstar (C1 s0 σ xmax φ0) * Real.log d) *
          Real.log T +
        (2 * b * xmax * C5 K q + 2 * K * b * xmax + C4 K b xmax pstar (C2 s0 xmax φ0)) := by sorry

end BastaniBayati.LassoBandit
