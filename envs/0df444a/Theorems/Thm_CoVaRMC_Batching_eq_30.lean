-- Prove2me | Theorems.Thm_CoVaRMC_Batching_eq_30
-- name    : CoVaRMC.Batching.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:55.648122+00:00
-- url     : https://prove2.me/theorems/a0c14042-7700-4720-91a4-026944ed8e28
-- title:
--   Proof of Theorem 3, p. 32, Equation (30) and lim σ̂(y_k) = √(β(1−β))
-- statement:
--   Work under the hypotheses of Theorem 3 (Assumption 1 with $v = \mathrm{VaR}_\alpha(X)$, $c = \mathrm{CoVaR}_{\alpha,\beta}$, the derivative bounds with constant $M$, and batch numbers $k \to \infty$, batch sizes $m \to \infty$, both $\ge 1$), but without any condition on $\sqrt k/m$. Fix $t \in \mathbb R$ and put
--   $$A = \frac{\sqrt{\beta(1-\beta)}}{f_{Y|X}(c\mid v)}, \qquad y_k = c + tAk^{-1/2}, \qquad c_{m,k}(t) = \frac{\sqrt k}{\hat\sigma(y_k)}\Big(\beta - \mathrm E\big[I\{\hat Y \le y_k\}\big]\Big).$$
--   Then:
--
--   1. for every $k, m$, the events $\big\{\frac{\sqrt k}{A}(\hat Y^{\mathrm{BE}} - c) \le t\big\}$ and $\{\hat F_k(y_k) \ge \beta\}$ coincide;
--   2. for every $k, m$ with $\hat\sigma(y_k) > 0$, the events $\{\hat F_k(y_k) \ge \beta\}$ and $\big\{\frac{\sqrt k}{\hat\sigma(y_k)}\big(\hat F_k(y_k) - \mathrm E[I\{\hat Y \le y_k\}]\big) \ge c_{m,k}(t)\big\}$ coincide;
--   3. $\displaystyle\lim_{n\to\infty} \hat\sigma(y_k) = \sqrt{\beta(1-\beta)}$.
--
--   Items 1 and 2 are the two equalities of Equation (30), as equalities of events (hence of probabilities); item 3 is the limit stated after it. Together they reduce the distribution of the normalized estimator to the Berry–Esseen bound of Lemma 4.
--
--   **Formalization Note.** The sequence is indexed by $\nu$, with $k = k(\nu)$, $m = m(\nu)$, $n = k(\nu)m(\nu)$; "$n \to \infty$" is $\nu \to \infty$. The hypothesis $\hat\sigma(y_k) > 0$ in item 2 is implicit on the page, which divides by $\hat\sigma(y_k)$; without it Lean's $a/0 = 0$ makes $c_{m,k}(t) = 0$ and the second equality fails. $c_{m,k}(t)$ is defined by its p. 31 formula, so $t = 0$ is allowed.
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 32, proof of Theorem 3, Equation (30) and the limit of σ̂(y_k); definitions of A, y_k, c_{m,k}(t) on p. 31

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching

/-- Proof of Theorem 3, p. 32, Equation (30) and `lim σ̂(y_k) = √(β(1-β))`: with
`A = √(β(1-β)) / f_{Y|X}(c | v)`, `y_k = c + tAk^{-1/2}` and
`c_{m,k}(t) = (√k/σ̂(y_k))(β - E[I{Ŷ ≤ y_k}])`,
(i) `{(√k/A)(Ŷ^BE - c) ≤ t} = {F̂_k(y_k) ≥ β}`;
(ii) `{F̂_k(y_k) ≥ β} = {(√k/σ̂(y_k))(F̂_k(y_k) - E[I{Ŷ ≤ y_k}]) ≥ c_{m,k}(t)}` when `σ̂(y_k) > 0`;
(iii) `σ̂(y_k) → √(β(1-β))`. -/
theorem eq_30 (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
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
    (∀ ν, {ω | √(k ν : ℝ) / Aconst D β v c * (YBE S α β (k ν) (m ν) ω - c) ≤ t} =
        {ω | β ≤ FkHat S α (k ν) (m ν) (yk c (Aconst D β v c) t (k ν)) ω}) ∧
    (∀ ν, 0 < sigmaHat P S α (m ν) (yk c (Aconst D β v c) t (k ν)) →
      {ω | β ≤ FkHat S α (k ν) (m ν) (yk c (Aconst D β v c) t (k ν)) ω} =
        {ω | cmk P S α β c (Aconst D β v c) t (k ν) (m ν) ≤
          √(k ν : ℝ) / sigmaHat P S α (m ν) (yk c (Aconst D β v c) t (k ν)) *
            (FkHat S α (k ν) (m ν) (yk c (Aconst D β v c) t (k ν)) ω - pHat P S α (m ν) (yk c (Aconst D β v c) t (k ν)))}) ∧
    Tendsto (fun ν => sigmaHat P S α (m ν) (yk c (Aconst D β v c) t (k ν))) atTop (𝓝 √(β * (1 - β))) := by sorry

end CoVaRMC.Batching
