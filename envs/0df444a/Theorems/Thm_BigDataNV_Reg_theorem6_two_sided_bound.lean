-- Prove2me | Theorems.Thm_BigDataNV_Reg_theorem6_two_sided_bound
-- name    : BigDataNV.Reg.theorem6_two_sided_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T05:27:45.944333+00:00
-- url     : https://prove2.me/theorems/a1d8c8d9-bbcd-4ee7-b400-bd4234086d26
-- title:
--   Theorem 6, p. 31 — |R_true − R̂| ≤ 2α_n + (4nα_n + M)√(ln(2/δ)/2n) for uniformly stable algorithms
-- statement:
--   Let $\mu$ be a probability distribution on a data space $\mathcal Z$, concentrated on a set $\mathcal Z_0$. Let $A$ be an algorithm mapping samples $S_n=(z_1,\dots,z_n)$ of size $n\ge1$ to hypotheses, let $\ell(f,z)$ be a loss, and for each $i$ let $A^{\setminus i}_{S_n}$ be a comparison hypothesis that does not depend on $z_i$. Assume, for all samples and points in $\mathcal Z_0$,
--   1. **uniform stability**: $|\ell(A_{S_n},z)-\ell(A^{\setminus i}_{S_n},z)|\le\alpha_n$ for all $i$;
--   2. **bounded loss**: $0\le\ell(A_{S_n},z)\le M$;
--   3. **measurability**: $(S_n,z)\mapsto\ell(A_{S_n},z)$ is measurable.
--
--   Write $R_{true}(A,S_n)=\mathbb E_{z}[\ell(A_{S_n},z)]$ and $\hat R(A,S_n)=\frac1n\sum_{i=1}^n\ell(A_{S_n},z_i)$. Then for every $\delta\in(0,1)$, with probability at least $1-\delta$ over an iid sample $S_n\sim\mu^n$,
--   $$|R_{true}(A,S_n)-\hat R(A,S_n)|\le 2\alpha_n+(4n\alpha_n+M)\sqrt{\frac{\ln(2/\delta)}{2n}} .$$
--
--   This two-sided bound converts the stability of an algorithm into a high-probability bound on its generalization gap; Theorem 2 applies it to (NV-reg).
--
--   **Formalization Note** The failure event, on which the gap exceeds the bound, is shown to have probability at most $\delta$. The comparison hypothesis $A^{\setminus i}$ is any map that ignores the $i$-th observation, which covers the algorithm run on $S_n^{\setminus i}$ (Definition 1) and the $1/n$-weighted leave-one-out problem of Theorems 4 and 5. Stability and boundedness are required on the support $\mathcal Z_0$ of $\mu$, which plays the role of the paper's $\mathcal Z$. Symmetry of $A$ is not assumed. Measurability is the standing convention of Appendix B ("all functions are measurable").
-- source:
--   Rudin & Vahn, The Big Data Newsvendor: Practical Insights from Machine Learning, MIT Sloan Working Paper 5036-13 (version of February 6, 2014), p. 31, Theorem 6, display (32), and the risks defined before it; proof p. 32

import Mathlib

open MeasureTheory

namespace BigDataNV.Reg

/-- Theorem 6, p. 31: a two-sided generalization bound for any algorithm that is uniformly stable
(with parameter `α`) and whose loss is bounded in `[0, M]`. The data space is `Z`, its support is
`Z0`, `A` maps a sample of size `n` to a hypothesis in `H`, and `Aloo i S` is the comparison
hypothesis that ignores the `i`-th observation. -/
theorem theorem6_two_sided_bound {Z H : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (Z0 : Set Z) (hμ : μ Z0ᶜ = 0)
    (ℓ : H → Z → ℝ) (n : ℕ) (hn : 1 ≤ n) (A : (Fin n → Z) → H)
    (Aloo : Fin n → (Fin n → Z) → H)
    (hloo : ∀ (i : Fin n) (S S' : Fin n → Z), (∀ j, j ≠ i → S j = S' j) → Aloo i S = Aloo i S')
    (α M : ℝ)
    (hstab : ∀ S : Fin n → Z, (∀ j, S j ∈ Z0) → ∀ i : Fin n, ∀ z ∈ Z0,
      |ℓ (A S) z - ℓ (Aloo i S) z| ≤ α)
    (hbound : ∀ S : Fin n → Z, (∀ j, S j ∈ Z0) → ∀ z ∈ Z0, 0 ≤ ℓ (A S) z ∧ ℓ (A S) z ≤ M)
    (hmeas : Measurable (fun q : (Fin n → Z) × Z => ℓ (A q.1) q.2))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin n => μ)
      {S | 2 * α + (4 * (n : ℝ) * α + M) * Real.sqrt (Real.log (2 / δ) / (2 * (n : ℝ))) <
        |(∫ z, ℓ (A S) z ∂μ) - (1 / (n : ℝ)) * ∑ i, ℓ (A S) (S i)|} ≤ ENNReal.ofReal δ := by sorry

end BigDataNV.Reg
