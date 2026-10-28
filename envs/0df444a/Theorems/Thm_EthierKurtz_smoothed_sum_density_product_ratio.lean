-- Prove2me | Theorems.Thm_EthierKurtz_smoothed_sum_density_product_ratio
-- name    : EthierKurtz.smoothed_sum_density_product_ratio
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:10:05.264448+00:00
-- url     : https://prove2.me/theorems/5b71093f-88cd-4718-995b-0bf697f7f845
-- title:
--   Cramér-type estimate for the conditional density of a half-difference
-- statement:
--   Let $G$ be a probability law on $\mathbb R$ with $\int e^{ax}\,dG(x)<\infty$ for $|a|\le a_0$, $\int x\,dG=0$, and suppose $G=p\,N(m,v)+(1-p)F_2$ with $0<p\le1$, $v>0$ and $F_2$ a probability law (a Gaussian component). Let $\Lambda=\log R$ be the cumulant generating function of $G$, $R(t)=\int e^{tx}dG$. Let $0<t_1$ with $2t_1<a_0$, $B\ge0$ such that $\tfrac12\le\Lambda''(t)\le2$ and $\int e^{tx}\,dN(m,v)\big/R(t)\ge\tfrac12$ for $|t|\le t_1$ and $|\Lambda'''(t)|\le B$ for $|t|\le 2t_1$. For a finite index set $\iota$ with $n=|\iota|$ and $\sigma>0$ let $f(a)=E\,\varphi_{n\sigma^2}(a-\sum_{i\in\iota}X_i)$ ($X_i$ i.i.d. $G$, $\varphi_V$ the $N(0,V)$ density) be the density of the smoothed sum $\sum_i(X_i+\sigma\eta_i)$ ($\eta_i$ i.i.d. $N(0,1)$), and put $\Lambda_\sigma(t)=\Lambda(t)+t^2\sigma^2/2$; $\Phi$ is the standard normal distribution function. There are $0<\kappa'\le1$, $K\ge0$ and $N_1$ such that for every finite $\iota$ with $n\ge2$, $n\ge N_1$, $0<\sigma\le1$ with $(1-\kappa')^{n-1}/\sigma\le1/n$, $|c|\le t_1/4$, $|\delta|\le t_1/4$ and $|t_c|\le t_1$ with $\Lambda_\sigma'(t_c)=c$, writing $E=K(n^{-1/2}+|\delta|+n|\delta|^3)$: $f(nc)>0$, $f(nc)\ge e^{-n(t_cc-\Lambda_\sigma(t_c))}(2\pi n\Lambda_\sigma''(t_c))^{-1/2}e^{-1}$ and
--
--   $$f(nc)^2e^{-n\delta^2/\Lambda_\sigma''(t_c)}e^{-E}\le f(n(c+\delta))\,f(n(c-\delta))\le f(nc)^2e^{-n\delta^2/\Lambda_\sigma''(t_c)}e^{E}.$$
--
--   Role: The estimate of the conditional density $d\mapsto f((T+d)/2)f((T-d)/2)$ of $S'-S''$ given $S'+S''=T=2nc$ needed at the nodes of the dyadic construction (Lemma 2 (b) at $c\pm\delta$ with the saddle point $t_c$).
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Section 3, Lemma 2 and its proof, pp. 38-40, formulas (b)-(c), applied to the node construction on p. 40

import Mathlib

namespace EthierKurtz

theorem smoothed_sum_density_product_ratio :
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
                                            ∀ (ι : Type) [inst : Fintype ι] (σ c δ tc : ℝ),
                                              (0 : ℝ) < σ →
                                                σ ≤ (1 : ℝ) →
                                                  N1 ≤ ↑(Fintype.card ι) →
                                                    (2 : ℕ) ≤ Fintype.card ι →
                                                      ((1 : ℝ) - κ') ^ (Fintype.card ι - (1 : ℕ)) / σ ≤
                                                          (1 : ℝ) / ↑(Fintype.card ι) →
                                                        |c| ≤ t1 / (4 : ℝ) →
                                                          |δ| ≤ t1 / (4 : ℝ) →
                                                            |tc| ≤ t1 →
                                                              deriv (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) tc +
                                                                    tc * σ ^ (2 : ℕ) =
                                                                  c →
                                                                (0 : ℝ) <
                                                                    ∫ (y : ℝ),
                                                                      ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                        (Real.toNNReal (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                        (↑(Fintype.card ι) * c -
                                                                          y) ∂MeasureTheory.Measure.map
                                                                        (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                        (MeasureTheory.Measure.pi fun (x : ι) => G) ∧
                                                                  Real.exp
                                                                            (-(↑(Fintype.card ι) *
                                                                                (tc * c -
                                                                                  (ProbabilityTheory.cgf (fun (x : ℝ) => x)
                                                                                      G tc +
                                                                                    tc ^ (2 : ℕ) * σ ^ (2 : ℕ) /
                                                                                      (2 : ℝ))))) *
                                                                          ((√((2 : ℝ) * Real.pi * ↑(Fintype.card ι)))⁻¹ *
                                                                            (√(iteratedDeriv (2 : ℕ)
                                                                                    (ProbabilityTheory.cgf
                                                                                      (fun (x : ℝ) => x) G)
                                                                                    tc +
                                                                                  σ ^ (2 : ℕ)))⁻¹) *
                                                                        Real.exp (-1 : ℝ) ≤
                                                                      ∫ (y : ℝ),
                                                                        ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                          (Real.toNNReal (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                          (↑(Fintype.card ι) * c -
                                                                            y) ∂MeasureTheory.Measure.map
                                                                          (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                          (MeasureTheory.Measure.pi fun (x : ι) => G) ∧
                                                                    (∫ (y : ℝ),
                                                                            ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                              (Real.toNNReal
                                                                                (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                              (↑(Fintype.card ι) * (c + δ) -
                                                                                y) ∂MeasureTheory.Measure.map
                                                                              (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                              (MeasureTheory.Measure.pi fun (x : ι) => G)) *
                                                                          ∫ (y : ℝ),
                                                                            ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                              (Real.toNNReal
                                                                                (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                              (↑(Fintype.card ι) * (c - δ) -
                                                                                y) ∂MeasureTheory.Measure.map
                                                                              (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                              (MeasureTheory.Measure.pi fun (x : ι) => G) ≤
                                                                        (∫ (y : ℝ),
                                                                                ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                                  (Real.toNNReal
                                                                                    (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                                  (↑(Fintype.card ι) * c -
                                                                                    y) ∂MeasureTheory.Measure.map
                                                                                  (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                                  (MeasureTheory.Measure.pi fun (x : ι) =>
                                                                                    G)) ^
                                                                              (2 : ℕ) *
                                                                            Real.exp
                                                                              (-(↑(Fintype.card ι) * δ ^ (2 : ℕ) /
                                                                                  (iteratedDeriv (2 : ℕ)
                                                                                      (ProbabilityTheory.cgf
                                                                                        (fun (x : ℝ) => x) G)
                                                                                      tc +
                                                                                    σ ^ (2 : ℕ)))) *
                                                                          Real.exp
                                                                            (K *
                                                                              ((1 : ℝ) / √↑(Fintype.card ι) + |δ| +
                                                                                ↑(Fintype.card ι) * |δ| ^ (3 : ℕ))) ∧
                                                                      (∫ (y : ℝ),
                                                                                ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                                  (Real.toNNReal
                                                                                    (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                                  (↑(Fintype.card ι) * c -
                                                                                    y) ∂MeasureTheory.Measure.map
                                                                                  (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                                  (MeasureTheory.Measure.pi fun (x : ι) =>
                                                                                    G)) ^
                                                                              (2 : ℕ) *
                                                                            Real.exp
                                                                              (-(↑(Fintype.card ι) * δ ^ (2 : ℕ) /
                                                                                  (iteratedDeriv (2 : ℕ)
                                                                                      (ProbabilityTheory.cgf
                                                                                        (fun (x : ℝ) => x) G)
                                                                                      tc +
                                                                                    σ ^ (2 : ℕ)))) *
                                                                          Real.exp
                                                                            (-(K *
                                                                                ((1 : ℝ) / √↑(Fintype.card ι) + |δ| +
                                                                                  ↑(Fintype.card ι) * |δ| ^ (3 : ℕ)))) ≤
                                                                        (∫ (y : ℝ),
                                                                            ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                              (Real.toNNReal
                                                                                (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                              (↑(Fintype.card ι) * (c + δ) -
                                                                                y) ∂MeasureTheory.Measure.map
                                                                              (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                              (MeasureTheory.Measure.pi fun (x : ι) => G)) *
                                                                          ∫ (y : ℝ),
                                                                            ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                              (Real.toNNReal
                                                                                (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                              (↑(Fintype.card ι) * (c - δ) -
                                                                                y) ∂MeasureTheory.Measure.map
                                                                              (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                              (MeasureTheory.Measure.pi fun (x : ι) => G) := by sorry

end EthierKurtz
