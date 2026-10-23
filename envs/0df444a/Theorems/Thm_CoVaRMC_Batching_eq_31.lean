-- Prove2me | Theorems.Thm_CoVaRMC_Batching_eq_31
-- name    : CoVaRMC.Batching.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:05.909253+00:00
-- url     : https://prove2.me/theorems/dbfbd6c4-4e5d-4b8d-875f-cb8cf5ab193a
-- title:
--   Proof of Theorem 3, p. 32, Equation (31) — Pr{√k/A (Ŷ^BE − CoVaRα,β) ≤ t} = O(k^{−1/2}) + Φ(−c_{m,k}(t))
-- statement:
--   Work under the hypotheses of Theorem 3 without any condition on $\sqrt k/m$, and let $A$, $y_k$ and $c_{m,k}(t)$ be as in Equation (30). For every $t \in \mathbb R$ there is a constant $C$ such that, for all sufficiently large $n$,
--   $$\left|\Pr\left\{\frac{\sqrt k}{A}\big(\hat Y^{\mathrm{BE}} - \mathrm{CoVaR}_{\alpha,\beta}\big) \le t\right\} - \Phi\big(-c_{m,k}(t)\big)\right| \le \frac{C}{\sqrt k},$$
--   i.e. $\Pr\{\frac{\sqrt k}{A}(\hat Y^{\mathrm{BE}} - \mathrm{CoVaR}_{\alpha,\beta}) \le t\} = O(k^{-1/2}) + \Phi(-c_{m,k}(t))$, where $\Phi$ is the standard normal distribution function.
--
--   Both regimes of Theorem 3 follow from this expansion once the behaviour of $c_{m,k}(t)$ is known (Equation (32)).
--
--   **Formalization Note.** The sequence is indexed by $\nu$ with $n = k(\nu)m(\nu)$; $O(k^{-1/2})$ is "eventually bounded by $C/\sqrt k$", with $C$ depending on $t$ and the model but not on $\nu$.
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 32, proof of Theorem 3, Equation (31)

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching

/-- Proof of Theorem 3, p. 32, Equation (31):
`Pr{(√k/A)(Ŷ^BE - c) ≤ t} = O(k^{-1/2}) + Φ(-c_{m,k}(t))`. -/
theorem eq_31 (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β)
    (M : ℝ) (hM : 0 < M)
    (hM1 : ∀ y ∈ 𝒴, |deriv (fun x => Fc y x) v| ≤ M)
    (hM2 : ∀ x : ℝ, ∀ y ∈ 𝒴, |deriv (deriv (fun x => Fc y x)) x| ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (k m : ℕ → ℕ) (hk0 : ∀ ν, 0 < k ν) (hm0 : ∀ ν, 0 < m ν)
    (hk : Tendsto k atTop atTop) (hm : Tendsto m atTop atTop)
    (t : ℝ) :
    ∃ C : ℝ, ∀ᶠ ν in atTop,
      |(P {ω | √(k ν : ℝ) / Aconst D β v c * (YBE S α β (k ν) (m ν) ω - c) ≤ t}).toReal
          - cdf (gaussianReal 0 1) (-cmk P S α β c (Aconst D β v c) t (k ν) (m ν))|
        ≤ C / √(k ν : ℝ) := by sorry

end CoVaRMC.Batching
