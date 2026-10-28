-- Prove2me | Theorems.Thm_EthierKurtz_kmt_gaussian_component_dyadic_coupling
-- name    : EthierKurtz.kmt_gaussian_component_dyadic_coupling
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:34:34.6639+00:00
-- url     : https://prove2.me/theorems/0f85c107-7836-420a-872b-50e822ca28d1
-- title:
--   KMT theorem for laws with a Gaussian component on dyadic horizons
-- statement:
--   Let $G=p\,N(m,v)+(1-p)F_2$ with $0<p\le1$, $v>0$, $F_2$ a probability law, and suppose $G$ has mean $0$, variance $1$ and $\int e^{ax}\,dG<\infty$ for $|a|\le a_0$. Then (with $F=G$) there are constants $C,K,\lambda>0$ such that for every $N$ there is a coupling $Q_N$ of $F^{\otimes 2^N}$ and $N(0,1)^{\otimes 2^N}$ on $\mathbb R^{2^N}\times\mathbb R^{2^N}$ with $$Q_N\Big(\max_{1\le k\le 2^N}|S_k-T_k|>C\log 2^N+x\Big)<Ke^{-\lambda x}\qquad(x>0)$$.
--
--   Role: the case of an absolutely continuous component (Theorem 1A) of the KMT theorem, applied to the law obtained after replacing the bounded part by a Gaussian.
-- source:
--   Komlós, Major, Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Section 3, Theorem 1A, pp. 38-41

import Mathlib
open MeasureTheory ProbabilityTheory

namespace EthierKurtz

theorem kmt_gaussian_component_dyadic_coupling (F2 : Measure ℝ) [IsProbabilityMeasure F2] (p m : ℝ)
    (v : NNReal) (hp0 : 0 < p) (hp1 : p ≤ 1) (hv : v ≠ 0) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)
    (hexp : (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ → Integrable (fun x : ℝ => Real.exp (a * x)) G))
    (hm : ∫ x, x ∂G = 0) (hvar : variance (fun x : ℝ => x) G = 1) :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin (2 ^ N) => G) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin (2 ^ N) => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 < x →
          Q {q | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C * Real.log ((2 ^ N : ℕ) : ℝ) + x <
            |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
              (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by sorry

end EthierKurtz
