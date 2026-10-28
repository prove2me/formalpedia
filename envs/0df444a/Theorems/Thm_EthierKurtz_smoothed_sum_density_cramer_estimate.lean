-- Prove2me | Theorems.Thm_EthierKurtz_smoothed_sum_density_cramer_estimate
-- name    : EthierKurtz.smoothed_sum_density_cramer_estimate
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:50:43.007192+00:00
-- url     : https://prove2.me/theorems/249a0b20-9182-4df6-b4fb-57018dac164a
-- title:
--   Cramér-type local estimate for the smoothed sum density (Lemma 2 (b))
-- statement:
--   Let $G$ be a probability law on $\mathbb R$ with $\int e^{ax}\,dG(x)<\infty$ for $|a|\le a_0$, $\int x\,dG=0$, and suppose $G=p\,N(m,v)+(1-p)F_2$ with $0<p\le1$, $v>0$ and $F_2$ a probability law (a Gaussian component). Let $\Lambda=\log R$ be the cumulant generating function of $G$, $R(t)=\int e^{tx}dG$. Let $0<t_1$ with $2t_1<a_0$, $B\ge0$ such that $\tfrac12\le\Lambda''(t)\le2$ and $\int e^{tx}\,dN(m,v)\big/R(t)\ge\tfrac12$ for $|t|\le t_1$ and $|\Lambda'''(t)|\le B$ for $|t|\le 2t_1$. For a finite index set $\iota$ with $n=|\iota|$ and $\sigma>0$ let $f(a)=E\,\varphi_{n\sigma^2}(a-\sum_{i\in\iota}X_i)$ ($X_i$ i.i.d. $G$, $\varphi_V$ the $N(0,V)$ density) be the density of the smoothed sum $\sum_i(X_i+\sigma\eta_i)$ ($\eta_i$ i.i.d. $N(0,1)$), and put $\Lambda_\sigma(t)=\Lambda(t)+t^2\sigma^2/2$; $\Phi$ is the standard normal distribution function. There are $0<\kappa'\le1$, $K\ge0$ and $N_1$ such that for every finite $\iota$ with $n\ge2$, $n\ge N_1$, every $0<\sigma\le1$ with $(1-\kappa')^{n-1}/\sigma\le1/n$ and $|\delta|\le t_1/2$, writing $L_2=\Lambda''(0)+\sigma^2$ and $E=K(n^{-1/2}+|\delta|+n|\delta|^3)$,
--
--   $$\frac{e^{-n\delta^2/(2L_2)}}{\sqrt{2\pi nL_2}}e^{-E}\le f(n\delta)\le\frac{e^{-n\delta^2/(2L_2)}}{\sqrt{2\pi nL_2}}e^{E}.$$
--
--   Role: Lemma 2 (b) for the smoothed variables $X_n+\sigma\eta_n$ of the proof of Theorem 1A, used for the root of each dyadic block.
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Section 3, Lemma 2 and its proof, pp. 38-40, formula (b)

import Mathlib

namespace EthierKurtz

theorem smoothed_sum_density_cramer_estimate :
    ∀ {G : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure G] {a0 : ℝ},
      (0 : ℝ) < a0 →
        (∀ (a : ℝ), |a| ≤ a0 → MeasureTheory.Integrable (fun (x : ℝ) => Real.exp (a * x)) G) →
          ∫ (x : ℝ), x ∂G = (0 : ℝ) →
            ∀ (p m : ℝ) (v : NNReal) (F2 : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure F2],
              (0 : ℝ) < p →
                p ≤ (1 : ℝ) →
                  (0 : NNReal) < v →
                    G = ENNReal.ofReal p • ProbabilityTheory.gaussianReal m v + ENNReal.ofReal ((1 : ℝ) - p) • F2 →
                      ∀ {t1 B : ℝ},
                        (0 : ℝ) < t1 →
                          (2 : ℝ) * t1 < a0 →
                            (0 : ℝ) ≤ B →
                              (∀ (t : ℝ),
                                  |t| ≤ t1 →
                                    (1 / 2 : ℝ) ≤ iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ∧
                                      iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ≤ (2 : ℝ)) →
                                (∀ t ∈ Set.Icc (-((2 : ℝ) * t1)) ((2 : ℝ) * t1),
                                    |iteratedDeriv (3 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t| ≤ B) →
                                  (∀ (t : ℝ),
                                      |t| ≤ t1 →
                                        (1 / 2 : ℝ) ≤
                                          ProbabilityTheory.mgf (fun (x : ℝ) => x) (ProbabilityTheory.gaussianReal m v) t /
                                            ProbabilityTheory.mgf (fun (x : ℝ) => x) G t) →
                                    ∃ (κ' : ℝ) (K : ℝ) (N1 : ℝ),
                                      (0 : ℝ) < κ' ∧
                                        κ' ≤ (1 : ℝ) ∧
                                          (0 : ℝ) ≤ K ∧
                                            ∀ (ι : Type) [inst : Fintype ι] (σ δ : ℝ),
                                              (0 : ℝ) < σ →
                                                σ ≤ (1 : ℝ) →
                                                  N1 ≤ ↑(Fintype.card ι) →
                                                    (2 : ℕ) ≤ Fintype.card ι →
                                                      ((1 : ℝ) - κ') ^ (Fintype.card ι - (1 : ℕ)) / σ ≤
                                                          (1 : ℝ) / ↑(Fintype.card ι) →
                                                        |δ| ≤ t1 / (2 : ℝ) →
                                                          (√((2 : ℝ) * Real.pi * ↑(Fintype.card ι)))⁻¹ *
                                                                    (√(iteratedDeriv (2 : ℕ)
                                                                            (ProbabilityTheory.cgf (fun (x : ℝ) => x) G)
                                                                            (0 : ℝ) +
                                                                          σ ^ (2 : ℕ)))⁻¹ *
                                                                  Real.exp
                                                                    (-(↑(Fintype.card ι) * δ ^ (2 : ℕ) /
                                                                        ((2 : ℝ) *
                                                                          (iteratedDeriv (2 : ℕ)
                                                                              (ProbabilityTheory.cgf (fun (x : ℝ) => x) G)
                                                                              (0 : ℝ) +
                                                                            σ ^ (2 : ℕ))))) *
                                                                Real.exp
                                                                  (-(K *
                                                                      ((1 : ℝ) / √↑(Fintype.card ι) + |δ| +
                                                                        ↑(Fintype.card ι) * |δ| ^ (3 : ℕ)))) ≤
                                                              ∫ (y : ℝ),
                                                                ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                  (Real.toNNReal (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                  (↑(Fintype.card ι) * δ -
                                                                    y) ∂MeasureTheory.Measure.map
                                                                  (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                  (MeasureTheory.Measure.pi fun (x : ι) => G) ∧
                                                            ∫ (y : ℝ),
                                                                ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                  (Real.toNNReal (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                  (↑(Fintype.card ι) * δ -
                                                                    y) ∂MeasureTheory.Measure.map
                                                                  (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                  (MeasureTheory.Measure.pi fun (x : ι) => G) ≤
                                                              (√((2 : ℝ) * Real.pi * ↑(Fintype.card ι)))⁻¹ *
                                                                    (√(iteratedDeriv (2 : ℕ)
                                                                            (ProbabilityTheory.cgf (fun (x : ℝ) => x) G)
                                                                            (0 : ℝ) +
                                                                          σ ^ (2 : ℕ)))⁻¹ *
                                                                  Real.exp
                                                                    (-(↑(Fintype.card ι) * δ ^ (2 : ℕ) /
                                                                        ((2 : ℝ) *
                                                                          (iteratedDeriv (2 : ℕ)
                                                                              (ProbabilityTheory.cgf (fun (x : ℝ) => x) G)
                                                                              (0 : ℝ) +
                                                                            σ ^ (2 : ℕ))))) *
                                                                Real.exp
                                                                  (K *
                                                                    ((1 : ℝ) / √↑(Fintype.card ι) + |δ| +
                                                                      ↑(Fintype.card ι) * |δ| ^ (3 : ℕ))) := by sorry

end EthierKurtz
