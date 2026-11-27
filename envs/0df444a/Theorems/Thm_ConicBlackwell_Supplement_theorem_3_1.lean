-- Prove2me | Theorems.Thm_ConicBlackwell_Supplement_theorem_3_1
-- name    : ConicBlackwell.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:47:46.088634+00:00
-- url     : https://prove2.me/theorems/35a49287-c214-53d8-a593-ffb8f008ba37
-- title:
--   Theorem 3.1 — CBA average regret $\le2\kappa L\sqrt{\sum\omega_t^2}/\sum\omega_t$ via $d(u_T,\mathcal C^\circ)\le\sqrt2L\sqrt{\sum\omega_t^2}$ (corrected: constants $\sqrt2L$ and $2\kappa L$)
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a nonempty convex compact set, $\kappa=\max_{x\in\mathcal X}\|x\|_2$, $\mathcal C=\operatorname{cone}(\{\kappa\}\times\mathcal X)$ and $\mathcal C^\circ$ its polar. Let $x_0,x_1\in\mathcal X$, let $(\omega_t)_{t\ge1}$ be positive payoff weights, and let $(x_t)_{t\ge1}$, $(u_t)_{t\ge0}$ be the decisions and aggregate payoffs of CBA with payoff weights $\omega$ on the losses $(f_t)_{t\ge1}$, so that $u_T=\sum_{t=1}^T\omega_tv_t$ with $v_t=(\langle f_t,x_t\rangle/\kappa,-f_t)$. Let $T\ge1$ and $\|f_t\|_2\le L$ for $1\le t\le T$. Then
--
--   1. the $\omega$-weighted regret is controlled by the distance of $u_T$ to $\mathcal C^\circ$:
--   $$
--   \sum_{t=1}^T\omega_t\langle f_t,x_t\rangle-\min_{x\in\mathcal X}\sum_{t=1}^T\omega_t\langle f_t,x\rangle\ \le\ \sqrt2\,\kappa\,d(u_T,\mathcal C^\circ);
--   $$
--   2. that distance grows at most like the $\ell_2$ norm of the weights:
--   $$
--   d(u_T,\mathcal C^\circ)\ \le\ \sqrt2\,L\sqrt{\textstyle\sum_{t=1}^T\omega_t^2};
--   $$
--   3. hence, with $S_T=\sum_{t=1}^T\omega_t$,
--   $$
--   \frac{\sum_{t=1}^T\omega_t\langle f_t,x_t\rangle-\min_{x\in\mathcal X}\sum_{t=1}^T\omega_t\langle f_t,x\rangle}{S_T}\ \le\ 2\kappa L\,\frac{\sqrt{\sum_{t=1}^T\omega_t^2}}{\sum_{t=1}^T\omega_t}.
--   $$
--
--   So CBA, with the same weights on decisions and payoffs, is a no-regret algorithm for every weighting with $\sqrt{\sum\omega_t^2}=o(\sum\omega_t)$, for instance $\omega_t=t^p$; this generalizes the uniform-weight guarantee of Abernethy, Bartlett and Hazan (2011).
--
--   The page states clauses 1 and 2 as $O(\kappa\,d(u_T,\mathcal C^\circ))$ and $O(L\sqrt{\sum\omega_t^2})$; the explicit constants are those of the proof (p.8), with clause 2 corrected. The page prints $\sqrt2\kappa L$ in clause 3, and the proof claims $d(u_T,\mathcal C^\circ)\le L\sqrt{\sum\omega_t^2}$ from $\|v_t\|_2\le L$; both are false: for $\mathcal X=[-1,1]$, $T=1$, $\omega_1=1$, $x_1=1$, $f_1=1$ one has $v_1=(1,-1)\in\mathcal C$, so $d(u_1,\mathcal C^\circ)=\sqrt2>L=1$ and the average regret is $2>\sqrt2$. Since $\|v_t\|_2\le\sqrt2\|f_t\|_2$ the correct constants are $\sqrt2L$ and $2\kappa L$, attained on that instance.
--
--   **Formalization Note** $\mathbb R^n$ is `E n`, $\kappa$ is `kappa X`, $\mathcal C^\circ$ is `target X`, $d$ is `Metric.infDist`, the min over $\mathcal X$ is an infimum (`weightedRegret`), and the run is `cbaX`/`cbaU`.
--
--   Differences from the source:
--   - correction: average-regret constant √2 κL → 2 κL; reason: X = [−1, 1], T = 1, ω₁ = 1, x₁ = 1, f₁ = 1 (so L = κ = 1): v₁ = (1, −1), the regret is ⟨f₁, x₁⟩ − min_{x∈[−1,1]} x = 2 > √2; the proof's ‖v_t‖₂ ≤ L (p.8) holds only as ‖v_t‖₂ ≤ √2‖f_t‖₂, giving √2κ · √2L = 2κL
--   - correction: d(u_T, C°) = O(L √(Σω_t²)), whose proof (p.8) gives the constant 1 → d(u_T, C°) ≤ √2 L √(Σω_t²); reason: same instance: v₁ ∈ C, so d(u₁, C°) = ‖v₁‖₂ = √2 > L √(ω₁²) = 1
--   - reading: the O(·) of clauses 1 and 2 → the explicit constants √2κ and √2L of the proof (p.8, with the correction above); reason: the O(·) carry no stated constants; the proof's constants are the statement's content, as in the published goal
--   - reading: payoff weights (ω_t) → 0 < ω t for t ≥ 1; reason: the paper's weights are positive (the published goal reads them so); clause 3 divides by S_T
--   - encoding: (4): ‖f‖ ≤ L for every (sub)gradient → ‖f t‖ ≤ L for 1 ≤ t ≤ T; reason: for a single regret minimizer, (4) bounds exactly the observed losses
--   - encoding: κ = max_{x∈X} ‖x‖₂, v_t = (⟨f_t, x_t⟩/κ, −f_t), min over X, d(·, C°), π_C → kappa X (sSup), payoff X x f with Lean's x/0 = 0, sInf (weightedRegret), Metric.infDist to target X, PerspEpi.projC; reason: sSup is the max and sInf the min on a nonempty compact X; κ = 0 only when X = {0}; C is nonempty closed convex, so projC is the projection
--   - encoding: x₁ ∈ X (initialization) and x₀ ∈ X 'arbitrary' in CHOOSEDECISION → universally quantified parameters in X; reason: the bound holds for every choice
--   - encoding: an adversary choosing f_{t+1} after seeing x_{t+1} → an arbitrary fixed loss sequence f : ℕ → ℝⁿ; reason: CBA is deterministic, so the bound for every sequence covers adaptive adversaries
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), Theorem 3.1, p.7 (proof pp.7–8; CBA, p.6; (4), p.5)

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_ConicBlackwell_weightedRegret
import Definitions.Def_ConicBlackwell_Supplement_cbaU
import Definitions.Def_ConicBlackwell_Supplement_cbaX
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell.Supplement

/-- **Theorem 3.1**, Grand-Clément & Kroer, arXiv:2202.12277v1, p.7, **corrected constants**.
Let `(x_t)_{t≥1}` be the decisions generated by CBA with payoff weights `(ω_t)_{t≥1}`, and
`S_T = Σ_{t=1}^T ω_t`.  Then
(a) `Σ_t ω_t⟨f_t, x_t⟩ − min_{x∈X} Σ_t ω_t⟨f_t, x⟩ ≤ √2 κ · d(u_T, C°)`,
(b) `d(u_T, C°) ≤ √2 L √(Σ_{t=1}^T ω_t²)`, and
(c) `(Σ_t ω_t⟨f_t, x_t⟩ − min_{x∈X} Σ_t ω_t⟨f_t, x⟩)/S_T ≤ 2 κ L √(Σ_t ω_t²) / Σ_t ω_t`.

The page states (a) and (b) as `O(κ · d(u_T, C°))` and `O(L √(Σ ω_t²))`; the explicit constants
are the proof's (p.8), with (b) corrected.  The page prints `√2 κ L` in (c) and the proof claims
`d(u_T, C°) ≤ L √(Σ ω_t²)` via `‖v_t‖₂ ≤ L`; both are false: on `X = [−1, 1]`, `T = 1`, `ω₁ = 1`,
`x₁ = 1`, `f₁ = 1`, `v₁ = (1, −1) ∈ C`, so `d(u₁, C°) = √2 > L = 1` and the average regret is
`2 > √2`.  Since `‖v_t‖₂ ≤ √2 ‖f_t‖₂`, the correct constants are `√2 L` and `2 κ L`.

Formalization Note: `X ⊂ ℝⁿ` nonempty, convex, compact; `κ = kappa X`; `C° = target X`;
`d = Metric.infDist`; `L` bounds `‖f_t‖₂` for `1 ≤ t ≤ T` (the paper's (4)); payoff weights are
positive; the run is `cbaX`/`cbaU` (CBA, no projection in the update) from `u₀ = 0` and an
arbitrary first decision `x₁ ∈ X`; the min over `X` is `sInf` (`weightedRegret`). -/
theorem theorem_3_1 {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty) (hXc : IsCompact X)
    (hXcv : Convex ℝ X) (x₀ x₁ : E n) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X)
    (ω : ℕ → ℝ) (hω : ∀ t, 1 ≤ t → 0 < ω t)
    (f : ℕ → E n) (L : ℝ) (T : ℕ) (hT : 1 ≤ T) (hf : ∀ t ∈ Finset.Icc 1 T, ‖f t‖ ≤ L) :
    weightedRegret X ω f (cbaX X x₀ x₁ ω f) T ≤
        Real.sqrt 2 * kappa X * Metric.infDist (cbaU X x₀ x₁ ω f T) (target X) ∧
      Metric.infDist (cbaU X x₀ x₁ ω f T) (target X) ≤
        Real.sqrt 2 * L * Real.sqrt (∑ t ∈ Finset.Icc 1 T, ω t ^ 2) ∧
      weightedRegret X ω f (cbaX X x₀ x₁ ω f) T / (∑ t ∈ Finset.Icc 1 T, ω t) ≤
        2 * kappa X * L * Real.sqrt (∑ t ∈ Finset.Icc 1 T, ω t ^ 2) /
          (∑ t ∈ Finset.Icc 1 T, ω t) := by sorry

end ConicBlackwell.Supplement
