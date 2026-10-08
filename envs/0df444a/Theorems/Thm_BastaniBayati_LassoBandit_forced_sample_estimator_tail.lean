-- Prove2me | Theorems.Thm_BastaniBayati_LassoBandit_forced_sample_estimator_tail
-- name    : BastaniBayati.LassoBandit.forced_sample_estimator_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T09:18:25.226723+00:00
-- url     : https://prove2.me/theorems/ffc0cf37-d599-46c6-ad80-b6a66c4bd150
-- title:
--   Tail inequality for the forced-sample estimator of an optimal arm
-- statement:
--   Work in Bastani and Bayati's model: covariates $X_t$ i.i.d. from $\mathcal P_X$ on $\mathcal X\subseteq\mathbb R^d$, independent $\sigma$-subgaussian noises $\varepsilon_{i,t}$ ($\sigma>0$) independent of the covariates, and Assumptions 1–4 with constants $x_{\max}, b, C_0, h, p_*, \phi_0$ and arm partition $\mathcal K_{opt}\cup\mathcal K_{sub}$; let $K\ge2$, $d>2$, and let $s_0$ be the sparsity parameter.
--
--   Let $q\in\mathbb Z^+$ with $q\ge4\lceil q_0\rceil$, $\lambda_1=\phi_0^2p_*h/(64s_0x_{\max})$, and let $\mathcal T_{i,t}$ be the forced-sample times of arm $i$ up to time $t$ (Eq. (2)). The forced-sample estimator $\hat\beta(\mathcal T_{i,t},\lambda_1)$ is the LASSO estimator trained on the covariates $X_s$ and the rewards $X_s^\top\beta_i+\varepsilon_{i,s}$ of arm $i$ at the times $s\in\mathcal T_{i,t}$. For every optimal arm $i\in\mathcal K_{opt}$ and every $t\ge(Kq)^2$,
--   $$\Pr\Big[\|\hat\beta(\mathcal T_{i,t},\lambda_1)-\beta_i\|_1>\frac{h}{4x_{\max}}\Big]\le\frac{5}{t^4}.$$
--
--   This is Proposition 2 of Bastani and Bayati: after $O(\log t)$ forced samples, the forced-sample estimator of each arm is within $h/(4x_{\max})$ of the truth with high probability, enough to separate arms whose rewards differ by the margin $h$.
--
--   **Formalization Note** The page states this for all $i\in[K]$; the statement is restricted to $i\in\mathcal K_{opt}$ because the compatibility assumption (Assumption 4) and the region $U_i$ on which the proof rests exist only for optimal arms, and without them the claim fails for a suboptimal arm whose parameter is not identifiable from the covariates. At the forced times of arm $i$ the algorithm plays arm $i$, so the statement needs no trajectory. The estimator is an arbitrary LASSO minimizer.
-- source:
--   Bastani & Bayati, Online Decision Making with High-Dimensional Covariates, Operations Research 68(1):276–294 (2020), doi:10.1287/opre.2019.1902, p. 286, Proposition 2 (q0 as displayed with Theorem 1, p. 285)

import Mathlib
import Definitions.Def_BastaniBayati_LassoBandit_Basic
import Definitions.Def_BastaniBayati_LassoBandit_Model
import Definitions.Def_BastaniBayati_LassoBandit_Constants
import Definitions.Def_BastaniBayati_LassoBandit_Algorithm

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace BastaniBayati.LassoBandit

/-- **Proposition 2**, Bastani–Bayati, p. 286, stated for the optimal arms `i ∈ 𝒦_opt` (see the
moderation notes: the page says "for all `i ∈ [K]`", but Assumption 4 and the region `Uᵢ` on
which the proof sketch of §4.2 rests exist only for `i ∈ 𝒦_opt`). Under the model of §2.1 and
Assumptions 1–4, with `K ≥ 2`, `d > 2`, the forced-sample estimator `β̂(𝒯_{i,t}, λ₁)` — any LASSO
estimator on the forced samples `𝒯_{i,t} = 𝒯ᵢ ∩ [t]` of arm `i`, whose responses are
`X_sᵀβᵢ + ε_{i,s}` — satisfies `Pr[‖β̂(𝒯_{i,t}, λ₁) − βᵢ‖₁ > h/(4x_max)] ≤ 5/t⁴` when
`λ₁ = φ₀² p_* h/(64 s₀ x_max)`, `t ≥ (Kq)²` and `q ≥ 4⌈q₀⌉`. -/
theorem forced_sample_estimator_tail
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
    (q t : ℕ)
    (hq : 4 * ⌈q0 d xmax h pstar (C1 s0 σ xmax φ0) (C2 s0 xmax φ0)⌉₊ ≤ q)
    (ht : (K * q) ^ 2 ≤ t) (i : Fin K) (hi : i ∈ Kopt) :
    P {ω | h / (4 * xmax) < l1Norm (lassoEst sel (forcedUpTo K q i t) (fun s => X s ω)
        (fun s => X s ω ⬝ᵥ β i + ε i s ω) (lam1 s0 xmax h pstar φ0) - β i)} ≤
      ENNReal.ofReal (5 / (t : ℝ) ^ 4) := by sorry

end BastaniBayati.LassoBandit
