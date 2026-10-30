-- Prove2me | Theorems.Thm_BousquetElisseeff_KLReg_lemma_21_kl_instance
-- name    : BousquetElisseeff.KLReg.lemma_21_kl_instance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:44:57.955718+00:00
-- url     : https://prove2.me/theorems/ab7a51d3-7d2f-4cd5-9a3c-ecbf058376a1
-- title:
--   Lemma 21 for $N = K(\cdot, f_0)$: $K(f, f^{\setminus i}) + K(f^{\setminus i}, f) \le \frac{1}{\lambda m}\big(\ell(f^{\setminus i}, z_i) - \ell(f, z_i)\big)$
-- statement:
--   Let $\mu$ be a reference measure on a measurable space $\Theta$ and let $\mathcal F$ be the set of probability densities with respect to $\mu$. Let $r(\theta, z)$ be the base loss of the hypothesis $h_\theta$ on the example $z$, measurable in $\theta$, with $0 \le r(\theta,z) \le M$. For $g \in \mathcal F$ write $\ell(g,z) = \int_\Theta r(\theta,z)\,g(\theta)\,d\mu(\theta)$ (eq. (28)) and $K(g,g') = \int_\Theta g \ln(g/g')\,d\mu \in [0,\infty]$ for the relative entropy. Fix a prior $f_0 \in \mathcal F$, a parameter $\lambda > 0$, a sample $S = (z_1,\dots,z_m)$ and an index $i \in \{1,\dots,m\}$. Let $f$ be any minimizer over $\mathcal F$ of
--   $$R_r(g) = \frac1m \sum_{j=1}^m \ell(g,z_j) + \lambda K(g,f_0) \qquad (19) = (29),$$
--   and let $f^{\setminus i}$ be any minimizer over $\mathcal F$ of
--   $$R_r^{\setminus i}(g) = \frac1m \sum_{j\ne i} \ell(g,z_j) + \lambda K(g,f_0). \qquad (20)$$
--
--   Then both $K(f, f^{\setminus i})$ and $K(f^{\setminus i}, f)$ are finite and
--   $$K(f, f^{\setminus i}) + K(f^{\setminus i}, f) \le \frac{1}{\lambda m}\Big(\ell(f^{\setminus i}, z_i) - \ell(f, z_i)\Big).$$
--
--   This is the first inequality of Lemma 21 in the setting of §5.2.3, where the Bregman divergence of $K(\cdot, f_0)$ is $K$ itself (p. 518) and the Bregman divergence of the linear map $\ell(\cdot, z_i)$ is $0$. It is the inequality the proof of Theorem 24 obtains "by Lemma 21".
--
--   **Formalization Note** Finiteness of the two divergences is part of the conclusion, so the inequality between real numbers cannot hide an infinite value.
--
--   Differences from the source:
--   - reading: Lemma 21: 𝓕 a vector space, N a proper closed convex differentiable function, d_N(f, f^{\i}) + d_N(f^{\i}, f) ≤ (1/(λm))(ℓ(f^{\i}, z_i) − ℓ(f, z_i) − d_ℓ(f^{\i}, f)) ≤ (σ/(λm))|∆f(x_i)| → 𝓕 = densities, N = K(·, f₀), d_N = K, d_ℓ = 0: K(f, f′) + K(f′, f) ≤ (ℓ(f′, z_i) − ℓ(f, z_i))/(λm), both K finite; reason: the proof of Theorem 24 (p. 518) applies Lemma 21 to the convex set of densities, which is not a vector space, with d_K(.,f0) = K and ℓ linear; this item states that application. The second inequality of Lemma 21 needs σ-admissibility of a cost c(f(x), y), which the loss (28) does not have; Theorem 24's proof uses M-admissibility instead (milestones M2, M4)
--   - generalization: standing assumption "all sets are countable" (p. 501) → Θ any measurable space, Z any type, μ any measure; reason: no step of the argument uses countability; the countable case is an instance
--   - encoding: r a loss on 𝓗 × 𝓩 bounded by M (p. 518), costs nonnegative (p. 502), functions measurable (p. 501) → r : Θ → Z → ℝ with θ ↦ r θ z measurable and 0 ≤ r θ z ≤ M; reason: r(h_θ, z) depends on h only through θ; the bounds are the paper's standing nonnegative costs and its bound M
--   - encoding: regularization parameter λ (unqualified) → 0 < lam; reason: the objective and the bound M²/(λm) presuppose λ > 0
--   - encoding: f a minimizer of (19), f^{\i} a minimizer of (20) (Lemma 20, pp. 512–513) → IsKLRegMinimizer with weight 1/m over univ (f) and over univ.erase i (f′); reason: literal transcription of (19) and (20) with N = K(·, f₀)
--   - encoding: 𝓕 = probability distributions dominated by the reference measure, given by their densities (p. 517) → IsDensity μ g: g measurable, g ≥ 0, ∫ g dμ = 1; reason: this is the paper's 𝓕; densities equal μ-a.e. give the same ℓ and K
--   - encoding: K(g, g′) = ∫_Θ g ln(g/g′) dθ (p. 517) → relEnt μ g g′ = klDiv (g·μ) (g′·μ) ∈ [0, ∞]; reason: for probability measures Mathlib's klDiv is ∫ g ln(g/g′) when finite and +∞ otherwise; same values
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002) 499–526, Lemma 21, p. 513, as applied in the proof of Theorem 24, p. 518 (d_K(.,f0)(g, g′) = K(g, g′))

import Mathlib
import Definitions.Def_BousquetElisseeff_KLReg_IsDensity
import Definitions.Def_BousquetElisseeff_KLReg_relEnt
import Definitions.Def_BousquetElisseeff_KLReg_avgLoss
import Definitions.Def_BousquetElisseeff_KLReg_IsKLRegMinimizer

open MeasureTheory

namespace BousquetElisseeff.KLReg

/-- **Lemma 21 for the relative-entropy regularizer N = K(·, f₀)** (Lemma 21, as applied in the
proof of Theorem 24).
Bousquet & Elisseeff, *Stability and Generalization*, JMLR 2 (2002) 499–526, Lemma 21, p. 513: "Under the conditions of Lemma 20, when 𝓕 is a vector space and N is a
proper closed convex function from 𝓕 to R ∪ {−∞, +∞}, we have
d_N(f, f^{\i}) + d_N(f^{\i}, f) ≤ (1/(λm)) (ℓ(f^{\i}, z_i) − ℓ(f, z_i) − d_{ℓ(.,z_i)}(f^{\i}, f))
≤ (σ/(λm)) |∆f(x_i)|, when N and ℓ are differentiable." Proof of Theorem 24, p. 518: "Moreover,
the Bregman divergence associated to the relative entropy to f0 is d_{K(.,f0)}(g, g′) = K(g, g′).
We saw that ℓ is M-admissible thus, by Lemma 21 we get …"

Setting (all items): `μ` is a reference measure on a measurable space Θ, `r θ z` the base loss
r(h_θ, z), measurable in θ with `0 ≤ r ≤ M` (nonnegative costs, p. 502; bound M, p. 518),
`λ > 0`, `f₀` a density (the prior), `S : Fin m → Z` the sample z₁, …, z_m, `i` an index, and
`f` any minimizer over 𝓕 of (19) = (29): `(1/m) Σ_{j} ℓ(g, z_j) + λK(g, f₀)`.
For every minimizer `f'` over 𝓕 of (20), `(1/m) Σ_{j ≠ i} ℓ(g, z_j) + λK(g, f₀)` (the paper's
f^{\i}), both divergences K(f, f′), K(f′, f) are finite and
`K(f, f′) + K(f′, f) ≤ (ℓ(f′, z_i) − ℓ(f, z_i)) / (λm)`.

This is the first inequality of Lemma 21 with d_N = K (the Bregman divergence of K(·, f₀), p. 518)
and d_{ℓ(.,z_i)} = 0 (ℓ is linear in g, p. 518).

**Formalization Note.** Finiteness of both divergences is part of the conclusion, so the
`toReal` in the inequality cannot turn `+∞` into `0`. -/
theorem lemma_21_kl_instance {Θ Z : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (r : Θ → Z → ℝ)
    (M lam : ℝ) (f0 : Θ → ℝ) (hr_meas : ∀ z, Measurable (fun θ => r θ z))
    (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M) (hlam : 0 < lam) (hf0 : IsDensity μ f0)
    {m : ℕ} (S : Fin m → Z) (i : Fin m) (f : Θ → ℝ)
    (hf : IsKLRegMinimizer μ r f0 lam (1 / (m : ℝ)) Finset.univ S f)
    (f' : Θ → ℝ)
    (hf' : IsKLRegMinimizer μ r f0 lam (1 / (m : ℝ)) (Finset.univ.erase i) S f') :
    relEnt μ f f' ≠ ⊤ ∧ relEnt μ f' f ≠ ⊤ ∧
      (relEnt μ f f').toReal + (relEnt μ f' f).toReal
        ≤ (avgLoss μ r f' (S i) - avgLoss μ r f (S i)) / (lam * (m : ℝ)) := by sorry

end BousquetElisseeff.KLReg
