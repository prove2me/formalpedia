-- Prove2me | Theorems.Thm_BousquetElisseeff_KLReg_theorem_24_uniform_stability
-- name    : BousquetElisseeff.KLReg.theorem_24_uniform_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:46:41.332286+00:00
-- url     : https://prove2.me/theorems/1974893f-ecd5-4dfb-b783-3694e77618be
-- title:
--   Theorem 24: relative-entropy regularization has uniform stability $\beta \le M^2/(\lambda m)$
-- statement:
--   Let $\mu$ be a reference measure on a measurable space $\Theta$ and let $\mathcal F$ be the set of probability densities with respect to $\mu$. Let $r(\theta, z)$ be the loss of the base hypothesis $h_\theta$ on the example $z$, measurable in $\theta$, with $0 \le r(\theta,z) \le M$. For $g \in \mathcal F$ let $\ell(g,z) = \int_\Theta r(\theta,z)\,g(\theta)\,d\mu(\theta)$ and let $K(g,g') = \int_\Theta g \ln(g/g')\,d\mu \in [0,\infty]$ be the relative entropy. Fix a prior $f_0 \in \mathcal F$ and $\lambda > 0$. The algorithm $A$ maps a sample $S = (z_1,\dots,z_m)$ to
--   $$A_S = \arg\min_{g \in \mathcal F}\ \frac1m \sum_{j=1}^m \ell(g, z_j) + \lambda K(g, f_0). \qquad (29)$$
--
--   **Theorem.** For every sample $S$ of size $m \ge 1$, every index $i$, every minimizer $f$ of (29), and every example $z$:
--
--   1. for every value $A_{S^{\setminus i}}$ of the algorithm on the sample $S^{\setminus i}$ with the $i$-th point removed, i.e. every minimizer over $\mathcal F$ of $\frac{1}{m-1}\sum_{j\ne i} \ell(g,z_j) + \lambda K(g,f_0)$,
--   $$|\ell(f, z) - \ell(A_{S^{\setminus i}}, z)| \le \frac{M^2}{\lambda m};$$
--   2. for every minimizer $f^{\setminus i}$ over $\mathcal F$ of $\frac1m \sum_{j\ne i} \ell(g, z_j) + \lambda K(g, f_0)$ (eq. (20)),
--   $$|\ell(f, z) - \ell(f^{\setminus i}, z)| \le \frac{M^2}{\lambda m}.$$
--
--   In the language of Definition 6, $A$ has uniform stability $\beta \le M^2/(\lambda m)$ with respect to $\ell$. Combined with the exponential generalization bound for uniformly stable algorithms (Theorem 12 of the paper), this gives generalization guarantees for Gibbs/MAP-type posteriors with a relative-entropy penalty.
--
--   **Formalization Note** At $m = 1$ the weight $1/(m-1)$ is $1/0 = 0$ in Lean, so the algorithm on the empty sample returns a minimizer of $\lambda K(\cdot, f_0)$, the prior $f_0$; the bound holds there as well.
--
--   Differences from the source:
--   - reading: ‖ℓ(A_S, .) − ℓ(A_{S\i}, .)‖∞ ≤ β with A_{S\i} the algorithm run on S\i (Definition 6, p. 504), while the proof bounds the minimizer f^{\i} of (20) (weight 1/m) → the conjunction: clause (i) for every minimizer with weight 1/((m:ℝ) − 1) over univ.erase i, clause (ii) for every minimizer with weight 1/m over univ.erase i; reason: A_{S\i} is ambiguous between the two and neither bound implies the other; both are true at M²/(λm), so the item states both
--   - generalization: (29) on S\i for m − 1 ≥ 1 points → m = 1 included; the weight 1/((1:ℝ) − 1) = 0 makes A on the empty sample a minimizer of λK(·, f₀); reason: the paper's (29) is undefined for an empty sample; for m ≥ 2 the Lean clause is the paper's
--   - generalization: standing assumption "all sets are countable" (p. 501) → Θ any measurable space, Z any type, μ any measure; reason: no step of the argument uses countability; the countable case is an instance
--   - encoding: r a loss on 𝓗 × 𝓩 bounded by M (p. 518), costs nonnegative (p. 502), functions measurable (p. 501) → r : Θ → Z → ℝ with θ ↦ r θ z measurable and 0 ≤ r θ z ≤ M; reason: r(h_θ, z) depends on h only through θ; the bounds are the paper's standing nonnegative costs and its bound M
--   - encoding: regularization parameter λ (unqualified) → 0 < lam; reason: the objective and the bound M²/(λm) presuppose λ > 0
--   - encoding: arg min over 𝓕 (A_S, f, f^{\i}) → every g with IsKLRegMinimizer (objective compared in EReal); reason: the minimizer exists and is unique μ-a.e.; the bound is claimed for every minimizer, no existence hypothesis is added
--   - encoding: ‖ℓ(A_S, .) − ℓ(A_{S\i}, .)‖∞ ≤ β → ∀ z, |avgLoss μ r f z − avgLoss μ r f′ z| ≤ M²/(λm); reason: the sup norm over z is bounded by β iff every value is
--   - encoding: training set S = {z_1, …, z_m} ∈ 𝓩^m and S\i = {z_1, …, z_{i−1}, z_{i+1}, …, z_m} (pp. 501–502) → S : Fin m → Z, S\i as the index set Finset.univ.erase i with weight 1/((m:ℝ) − 1); reason: 𝓩^m is the set of m-tuples; A is symmetric with respect to S (p. 501), so the order of the remaining m − 1 points does not change A_{S\i}
--   - encoding: 𝓕 = probability distributions dominated by the reference measure, given by their densities (p. 517) → IsDensity μ g: g measurable, g ≥ 0, ∫ g dμ = 1; reason: this is the paper's 𝓕; densities equal μ-a.e. give the same ℓ and K
--   - encoding: K(g, g′) = ∫_Θ g ln(g/g′) dθ (p. 517) → relEnt μ g g′ = klDiv (g·μ) (g′·μ) ∈ [0, ∞]; reason: for probability measures Mathlib's klDiv is ∫ g ln(g/g′) when finite and +∞ otherwise; same values
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002) 499–526, Theorem 24, eq. (29), p. 518; Definition 6, eq. (7), p. 504

import Mathlib
import Definitions.Def_BousquetElisseeff_KLReg_IsDensity
import Definitions.Def_BousquetElisseeff_KLReg_relEnt
import Definitions.Def_BousquetElisseeff_KLReg_avgLoss
import Definitions.Def_BousquetElisseeff_KLReg_IsKLRegMinimizer

open MeasureTheory

namespace BousquetElisseeff.KLReg

/-- **Theorem 24: uniform stability M²/(λm) of relative-entropy regularization.**
Bousquet & Elisseeff, *Stability and Generalization*, JMLR 2 (2002) 499–526, Theorem 24, p. 518: "Let 𝓕 defined as above and let r be any loss function defined on
𝓗 × 𝓩, bounded by M. Let f0 be a fixed member of 𝓕. When ℓ is defined by (28), the learning
algorithm A defined by A_S = arg min_{g∈𝓕} (1/m) Σ_{i=1}^m ℓ(g, z_i) + λK(g, f0), (29) has
uniform stability β with respect to ℓ with β ≤ M²/(λm)."
Definition 6, p. 504: "An algorithm A has uniform stability β with respect to the loss function
ℓ if the following holds ∀S ∈ 𝓩^m, ∀i ∈ {1, …, m}, ‖ℓ(A_S, .) − ℓ(A_{S\i}, .)‖∞ ≤ β. (7)"

Setting (all items): `μ` is a reference measure on a measurable space Θ, `r θ z` the base loss
r(h_θ, z), measurable in θ with `0 ≤ r ≤ M` (nonnegative costs, p. 502; bound M, p. 518),
`λ > 0`, `f₀` a density (the prior), `S : Fin m → Z` the sample z₁, …, z_m, `i` an index, and
`f` any minimizer over 𝓕 of (19) = (29): `(1/m) Σ_{j} ℓ(g, z_j) + λK(g, f₀)`.
Then for every example `z`:
1. for every value `f'` of A_{S\i}, i.e. every minimizer over 𝓕 of (29) on the sample S\i,
   `(1/(m−1)) Σ_{j ≠ i} ℓ(g, z_j) + λK(g, f₀)`: `|ℓ(f, z) − ℓ(f′, z)| ≤ M²/(λm)`;
2. for every minimizer `f'` over 𝓕 of (20), `(1/m) Σ_{j ≠ i} ℓ(g, z_j) + λK(g, f₀)` (the f^{\i}
   of Lemma 20 used in the paper's proof): `|ℓ(f, z) − ℓ(f′, z)| ≤ M²/(λm)`.
Since `S` and `i` are arbitrary, this is (7) with β = M²/(λm), and `‖·‖∞` is the bound for
every `z`.

**Formalization Note.** Definition 6 compares A_S with A run on S\i (weight 1/(m−1)), while the
paper's proof bounds the minimizer f^{\i} of (20) (weight 1/m); the statement asserts the bound
for both. "arg min" is read as every minimizer (the minimizer exists and is unique μ-a.e.). At
`m = 1` the weight `1/((m:ℝ) − 1)` is `1/0 = 0` in Lean, so A on the empty sample is the
minimizer of λK(·, f₀), the prior f₀; the bound holds there. The paper's standing assumption
"all sets are countable" (p. 501) is dropped: Θ is any measurable space and μ any measure. -/
theorem theorem_24_uniform_stability {Θ Z : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (r : Θ → Z → ℝ)
    (M lam : ℝ) (f0 : Θ → ℝ) (hr_meas : ∀ z, Measurable (fun θ => r θ z))
    (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M) (hlam : 0 < lam) (hf0 : IsDensity μ f0)
    {m : ℕ} (S : Fin m → Z) (i : Fin m) (f : Θ → ℝ)
    (hf : IsKLRegMinimizer μ r f0 lam (1 / (m : ℝ)) Finset.univ S f) :
    (∀ f' : Θ → ℝ,
        IsKLRegMinimizer μ r f0 lam (1 / ((m : ℝ) - 1)) (Finset.univ.erase i) S f' →
        ∀ z : Z, |avgLoss μ r f z - avgLoss μ r f' z| ≤ M ^ 2 / (lam * (m : ℝ))) ∧
    (∀ f' : Θ → ℝ,
        IsKLRegMinimizer μ r f0 lam (1 / (m : ℝ)) (Finset.univ.erase i) S f' →
        ∀ z : Z, |avgLoss μ r f z - avgLoss μ r f' z| ≤ M ^ 2 / (lam * (m : ℝ))) := by sorry

end BousquetElisseeff.KLReg
