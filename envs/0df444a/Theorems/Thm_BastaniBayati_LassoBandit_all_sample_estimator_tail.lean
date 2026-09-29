-- Prove2me | Theorems.Thm_BastaniBayati_LassoBandit_all_sample_estimator_tail
-- name    : BastaniBayati.LassoBandit.all_sample_estimator_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T09:22:52.351343+00:00
-- url     : https://prove2.me/theorems/0e82eac3-81ea-4ec7-b206-3e8a861cd69a
-- title:
--   Tail inequality for the all-sample estimator of an optimal arm
-- statement:
--   Work in Bastani and Bayati's model under Assumptions 1–4 (constants $x_{\max}, b, C_0, h, p_*, \phi_0$, $\sigma>0$, sparsity $s_0$), with $K\ge2$ and $d>2$. Run the LASSO Bandit with $q\ge4\lceil q_0\rceil$, the $h$ of Assumption 3, $\lambda_1=\phi_0^2p_*h/(64s_0x_{\max})$ and $\lambda_{2,0}=[\phi_0^2/(2s_0)]\sqrt{1/(p_*C_1)}$, using any measurable LASSO selection rule and any measurable tie-breaking of the arg max. Let $\mathcal S_{i,t}$ be the (random) set of times up to $t$ at which arm $i$ was played.
--
--   For every optimal arm $i\in\mathcal K_{opt}$ and every $t\ge C_5$, the all-sample estimator $\hat\beta(\mathcal S_{i,t},\lambda_{2,t})$ with
--   $$\lambda_{2,t}=\frac{\phi_0^2}{2s_0}\sqrt{\frac{\log t+\log d}{p_*C_1(\phi_0)\,t}}$$
--   satisfies
--   $$\Pr\Big[\|\hat\beta(\mathcal S_{i,t},\lambda_{2,t})-\beta_i\|_1>16\sqrt{\frac{\log t+\log d}{p_*^3C_1(\phi_0)\,t}}\Big]<\frac2t+2\exp\Big[-\frac{p_*^2C_2(\phi_0)^2}{32}\cdot t\Big].$$
--
--   This is Proposition 3 of Bastani and Bayati: although the all-sample sets are chosen adaptively and are not i.i.d., the all-sample estimator of every optimal arm converges at rate $\sqrt{\log t/t}$.
--
--   **Formalization Note** The trajectory is the one defined in the Algorithm definition; the estimator on $\mathcal S_{i,t}$ is trained on the covariates and the observed rewards $X_s^\top\beta_i+\varepsilon_{i,s}$ at the times $s\in\mathcal S_{i,t}$, and is $0$ if $\mathcal S_{i,t}=\emptyset$. As in Theorem 1, the selection rule and the tie-breaking rule are required to be measurable, so that the trajectory and $\mathcal S_{i,t}$ are random variables, as the paper's probability space presupposes. The probability of a possibly non-measurable event is its outer measure.
-- source:
--   Bastani & Bayati, Online Decision Making with High-Dimensional Covariates, Operations Research 68(1):276–294 (2020), doi:10.1287/opre.2019.1902, p. 287, Proposition 3, Eq. (4)

import Mathlib
import Definitions.Def_BastaniBayati_LassoBandit_Basic
import Definitions.Def_BastaniBayati_LassoBandit_Model
import Definitions.Def_BastaniBayati_LassoBandit_Constants
import Definitions.Def_BastaniBayati_LassoBandit_Algorithm

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace BastaniBayati.LassoBandit

/-- **Proposition 3**, Bastani–Bayati, p. 287. Run the LASSO Bandit with Theorem 1's parameters
(`q ≥ 4⌈q₀⌉`, `h` of Assumption 3, `λ₁ = φ₀²p_*h/(64s₀x_max)`,
`λ₂,₀ = [φ₀²/(2s₀)]√(1/(p_*C₁))`), any (measurable) LASSO selection rule and any (measurable)
arg-max tie-breaking rule, so that the trajectory, and hence `𝒮_{i,t}`, is a random variable.
Under the model of §2.1 and Assumptions 1–4, with `K ≥ 2`, `d > 2`, for every optimal arm
`i ∈ 𝒦_opt` and `t ≥ C₅`, the all-sample estimator `β̂(𝒮_{i,t}, λ₂,ₜ)` with
`λ₂,ₜ = [φ₀²/(2s₀)]√((log t + log d)/(p_* C₁(φ₀) t))` satisfies
`Pr[‖β̂(𝒮_{i,t}, λ₂,ₜ) − βᵢ‖₁ > 16√((log t + log d)/(p_*³C₁(φ₀)t))]
  < 2/t + 2 exp[−(p_*²C₂(φ₀)²/32)·t]`. -/
theorem all_sample_estimator_tail
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
    (htb_meas : ∀ S : Finset (Fin K), Measurable (fun s : Fin K → ℝ => tb s S)) (q t : ℕ)
    (hq : 4 * ⌈q0 d xmax h pstar (C1 s0 σ xmax φ0) (C2 s0 xmax φ0)⌉₊ ≤ q)
    (ht : C5 K q ≤ t) (i : Fin K) (hi : i ∈ Kopt) :
    P {ω | 16 * Real.sqrt ((Real.log t + Real.log d) / (pstar ^ 3 * C1 s0 σ xmax φ0 * t)) <
        l1Norm (lassoEst sel
          (allSampleSet (lassoBanditArm sel tb q h (lam1 s0 xmax h pstar φ0)
            (lam20 s0 pstar φ0 (C1 s0 σ xmax φ0)) X ε β ω) i t)
          (fun s => X s ω) (fun s => X s ω ⬝ᵥ β i + ε i s ω)
          (φ0 ^ 2 / (2 * s0) *
            Real.sqrt ((Real.log t + Real.log d) / (pstar * C1 s0 σ xmax φ0 * t))) - β i)} <
      ENNReal.ofReal (2 / t + 2 * Real.exp (-(pstar ^ 2 * C2 s0 xmax φ0 ^ 2 / 32) * t)) := by sorry

end BastaniBayati.LassoBandit
