-- Prove2me | Theorems.Thm_BastaniBayati_LassoBandit_lasso_tail_inequality_iid_fraction
-- name    : BastaniBayati.LassoBandit.lasso_tail_inequality_iid_fraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T09:14:46.818768+00:00
-- url     : https://prove2.me/theorems/fd45d5b9-3afd-475a-be48-29a0e1c912fd
-- title:
--   LASSO tail inequality when a fraction of the samples is i.i.d.
-- statement:
--   Consider the linear model $W=\mathbf Z\beta+\varepsilon$ with rows $Z_t\in\mathbb R^d$ indexed by times $t$ on a filtered probability space: row $Z_t$ is $\mathcal F_t$-measurable, noise $\varepsilon_t$ is $\mathcal F_{t+1}$-measurable and $\sigma$-subgaussian conditionally on $\mathcal F_t$ ($\sigma>0$), every realization has $\|Z_t\|_\infty\le x_{\max}$ ($x_{\max}>0$), and $\|\beta\|_0=s_0\ge1$. Let $\mathcal A'\subseteq\mathcal A$ be finite sets of times such that the rows $\{Z_t : t\in\mathcal A'\}$ are i.i.d. with law $\mathcal P_Z$, and let $\Sigma=\mathbb E_{Z\sim\mathcal P_Z}[ZZ^\top]\in\mathcal C(\mathrm{supp}(\beta),\phi_1)$ for a constant $\phi_1>0$. Let $p>0$ and $\chi>0$.
--
--   If $d>1$, $|\mathcal A'|/|\mathcal A|\ge p/2$, $|\mathcal A|\ge 6\log d/(pC_2(\phi_1)^2)$ and $\lambda=\lambda(\chi,\phi_1\sqrt p/2)=\chi\phi_1^2p/(16s_0)$, then every LASSO estimator $\hat\beta(\mathcal A,\lambda)$ trained on the samples in $\mathcal A$ satisfies
--   $$\Pr\big[\|\hat\beta(\mathcal A,\lambda)-\beta\|_1>\chi\big]\le 2\exp\Big[-C_1\Big(\frac{\phi_1\sqrt p}{2}\Big)|\mathcal A|\chi^2+\log d\Big]+\exp\big[-pC_2(\phi_1)^2|\mathcal A|/2\big].$$
--
--   This is Lemma 1 of Bastani and Bayati: the LASSO converges on a sample that is only partly i.i.d., provided a constant fraction is. It is the step from Proposition 1 to the forced-sample and all-sample estimators.
--
--   **Formalization Note** $\mathcal A$ and $\mathcal A'$ are fixed (deterministic) sets of times, the literal reading of the lemma; the paper later applies it with random sets. $C_1$, $C_2$ are those of the Constants definition with $s_0=\|\beta\|_0$. Noise and boundedness are assumed on the times in $\mathcal A$ only.
-- source:
--   Bastani & Bayati, Online Decision Making with High-Dimensional Covariates, Operations Research 68(1):276–294 (2020), doi:10.1287/opre.2019.1902, p. 286, Lemma 1 (setting of §4.1, pp. 285–286)

import Mathlib
import Definitions.Def_BastaniBayati_LassoBandit_Basic
import Definitions.Def_BastaniBayati_LassoBandit_Constants

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace BastaniBayati.LassoBandit

/-- **Lemma 1**, Bastani–Bayati, p. 286 (setting of §4.1, pp. 285–286), with `𝒜' ⊆ 𝒜` fixed
index sets. Linear model `W = Zβ + ε` on a filtered probability space: row `Z_t` is
`ℱ_t`-measurable, `ε_t` is `ℱ_{t+1}`-measurable and `σ`-subgaussian conditionally on `ℱ_t`,
`‖Z_t‖_∞ ≤ x_max` for every realization (`t ∈ 𝒜`), `‖β‖₀ = s₀ ≥ 1`. The rows `{Z_t | t ∈ 𝒜'}` are
i.i.d. with law `𝒫_Z`, and `Σ ≡ E_{Z∼𝒫_Z}[ZZᵀ] ∈ 𝒞(supp(β), φ₁)` with `φ₁ > 0`. For `p > 0`,
`χ > 0`, if `d > 1`, `|𝒜'|/|𝒜| ≥ p/2`, `|𝒜| ≥ 6 log d/(p C₂(φ₁)²)` and
`λ = λ(χ, φ₁√p/2) = χφ₁²p/(16s₀)`, then every LASSO estimator `β̂(𝒜, λ)` on the samples in `𝒜`
satisfies `Pr[‖β̂(𝒜, λ) − β‖₁ > χ] ≤ 2 exp[−C₁(φ₁√p/2)|𝒜|χ² + log d] + exp[−p C₂(φ₁)²|𝒜|/2]`. -/
theorem lasso_tail_inequality_iid_fraction {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ℱ : Filtration ℕ mΩ) (Z : ℕ → Ω → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (β : Fin d → ℝ) (σ : ℝ≥0) (xmax : ℝ) (s0 : ℕ) (PZ : Measure (Fin d → ℝ))
    (A A' : Finset ℕ) (φ1 p χ : ℝ) (βhat : Ω → Fin d → ℝ)
    (hσ : 0 < σ) (hxmax : 0 < xmax) (hs0 : (supp β).card = s0) (hs0pos : 1 ≤ s0)
    (hφ1 : 0 < φ1) (hp : 0 < p) (hχ : 0 < χ) (hd : 1 < d)
    (hZ_adapted : ∀ t ∈ A, Measurable[ℱ t] (Z t))
    (hε_meas : ∀ t ∈ A, Measurable[ℱ (t + 1)] (ε t))
    (hε_int : ∀ t ∈ A, ∀ s : ℝ, Integrable (fun ω => Real.exp (s * ε t ω)) P)
    (hε_subg : ∀ t ∈ A, ∀ s : ℝ,
      P[fun ω => Real.exp (s * ε t ω) | ℱ t] ≤ᵐ[P] fun _ => Real.exp ((σ : ℝ) ^ 2 * s ^ 2 / 2))
    (hbound : ∀ t ∈ A, ∀ ω, ‖Z t ω‖ ≤ xmax)
    (hA'A : A' ⊆ A)
    (hiid : iIndepFun (fun t : A' => Z t) P) (hlaw : ∀ t ∈ A', P.map (Z t) = PZ)
    (hSigma : (fun a b => ∫ z, z a * z b ∂PZ : Matrix (Fin d) (Fin d) ℝ) ∈ compatSet (supp β) φ1)
    (hfrac : p / 2 ≤ (A'.card : ℝ) / A.card)
    (hsize : 6 * Real.log d / (p * C2 s0 xmax φ1 ^ 2) ≤ A.card)
    (hβhat : ∀ ω, IsLassoMinimizer (fun t : A => Z t ω) (fun t : A => Z t ω ⬝ᵥ β + ε t ω)
      (χ * φ1 ^ 2 * p / (16 * s0)) (βhat ω)) :
    P {ω | χ < l1Norm (βhat ω - β)} ≤
      ENNReal.ofReal (2 * Real.exp (-(C1 s0 σ xmax (φ1 * Real.sqrt p / 2)) * A.card * χ ^ 2
          + Real.log d) +
        Real.exp (-(p * C2 s0 xmax φ1 ^ 2 * A.card / 2))) := by sorry

end BastaniBayati.LassoBandit
