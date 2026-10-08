-- Prove2me | Theorems.Thm_AdamDyn_ConstStep_lemma_8_1
-- name    : AdamDyn.ConstStep.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:40.755769+00:00
-- url     : https://prove2.me/theorems/c60a2495-2ac5-4d47-aadf-7fe1b54d4505
-- title:
--   Lemma 8.1 — uniform $(1+s)$-moment bound on $H_\gamma(n+1,z,\xi)$ over $\|e_\gamma(n,z)\|\le R$ (corrected at $n=0$)
-- statement:
--   Assume Assumption 2.2, Assumption 2.5 (with limits $a,b$) and Assumption 4.2 ii) with $p=2$, and let $\varepsilon>0$. Then there is $\bar\gamma_0>0$ such that for every $R>0$ there is $s>0$ with
--
--   $$
--   \sup\Big\{ \mathbb E\big(\|H_\gamma(n+1,z,\xi)\|^{1+s}\big) : \gamma\in(0,\bar\gamma_0],\ n\in\mathbb N,\ z=(x,m,v)\in\mathcal Z_+,\ \|e_\gamma(n,z)\|\le R,\ m=0 \text{ if } n=0 \Big\} < \infty .
--   $$
--
--   Here $H_\gamma$ is the normalised Adam increment and $e_\gamma$ the debiasing map of §8.1. The bound is the moment estimate behind the uniform integrability of the truncated Adam increments (Lemma 8.2).
--
--   **Formalization Note** Two readings differ from the printed text. (1) The lemma cites "Assumption 4.2" without a value of $p$; the $v$-block of $H_\gamma$ is quadratic in $\nabla f$, so a $2(1+s)$-th moment is needed, which is Assumption 4.2 ii) with $p=2$, the setting of Theorem 4.3. (2) As printed, with the convention $e_\gamma(0,z)=z$, the case $n=0$ fails: for $z=(x,m,0)$ with $m\ne0$ the $x$-block of $H_\gamma(1,z,\xi)$ contains $\bar\alpha(\gamma)m/((1-\bar\alpha(\gamma))(\varepsilon+|\nabla f|))$, which is unbounded as $\gamma\downarrow0$. The only state at $n=0$ that the iterates visit is $z^\gamma_0=(x_0,0,0)$, so the supremum at $n=0$ is restricted to $m=0$; this is the case Lemma 8.2 uses. Moments are lower Lebesgue integrals and $\|\cdot\|$ is the Euclidean norm of $\mathbb R^{3d}$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 21, Lemma 8.1, Eq. (8.1)

import Mathlib
import Definitions.Def_AdamDyn_ConstStep_StochasticModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace AdamDyn.ConstStep

/-- Lemma 8.1 (p. 21), corrected at `n = 0`: there is `γ̄0 > 0` such that for every `R > 0`
there is `s > 0` with
`sup { E‖H_γ(n+1, z, ξ)‖^{1+s} : γ ∈ (0, γ̄0], n ∈ ℕ, z ∈ 𝒵₊, ‖e_γ(n, z)‖ ≤ R } < ∞`,
where for `n = 0` the supremum is over `z = (x, 0, v)` (as printed, with `e_γ(0, z) = z` and
`m ≠ 0`, the `x`-block of `H_γ(1, z, ξ)` is of order `|m|/(1 − ᾱ(γ))` and the supremum is
infinite). Assumption 4.2 is read as 4.2 ii) with `p = 2`. -/
theorem lemma_8_1 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (gf : E d → Ξ → E d) (αbar βbar : ℝ → ℝ) (a b ε : ℝ)
    (h22 : Assumption22 μ f gf)
    (h25 : Assumption25 αbar βbar a b)
    (h42 : Assumption42ii μ gf 2)
    (hε : 0 < ε) :
    ∃ γ0 : ℝ, 0 < γ0 ∧ ∀ R : ℝ, 0 < R → ∃ s : ℝ, 0 < s ∧
      (⨆ (γ : ℝ) (_ : γ ∈ Set.Ioc 0 γ0) (n : ℕ) (z : Z d)
          (_ : InZplus z ∧ zNorm (eGamma αbar βbar γ n z) ≤ R ∧ (n = 0 → z.2.1 = 0)),
        ∫⁻ ξ, ENNReal.ofReal (zNorm (HGamma gf αbar βbar ε γ (n + 1) z ξ)) ^ (1 + s) ∂μ) < ⊤ := by sorry

end AdamDyn.ConstStep
