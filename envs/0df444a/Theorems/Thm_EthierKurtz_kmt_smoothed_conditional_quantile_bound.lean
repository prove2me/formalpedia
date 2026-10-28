-- Prove2me | Theorems.Thm_EthierKurtz_kmt_smoothed_conditional_quantile_bound
-- name    : EthierKurtz.kmt_smoothed_conditional_quantile_bound
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:47:49.306693+00:00
-- url     : https://prove2.me/theorems/5c3fc80f-8377-4075-96a6-df8eabd3858e
-- title:
--   KMT node estimate for smoothed sums with a Gaussian component
-- statement:
--   Let $G$ be a probability law on $\mathbb R$ with $\int e^{ax}\,dG(x)<\infty$ for $|a|\le a_0$, $\int x\,dG=0$, and suppose $G=p\,N(m,v)+(1-p)F_2$ with $0<p\le1$, $v>0$ and $F_2$ a probability law (a Gaussian component). Let $\Lambda=\log R$ be the cumulant generating function of $G$, $R(t)=\int e^{tx}dG$. Let $0<t_1$ with $2t_1<a_0$, $B\ge0$ such that $\tfrac12\le\Lambda''(t)\le2$ and $\int e^{tx}\,dN(m,v)\big/R(t)\ge\tfrac12$ for $|t|\le t_1$ and $|\Lambda'''(t)|\le B$ for $|t|\le 2t_1$. For a finite index set $\iota$ with $n=|\iota|$ and $\sigma>0$ let $f(a)=E\,\varphi_{n\sigma^2}(a-\sum_{i\in\iota}X_i)$ ($X_i$ i.i.d. $G$, $\varphi_V$ the $N(0,V)$ density) be the density of the smoothed sum $\sum_i(X_i+\sigma\eta_i)$ ($\eta_i$ i.i.d. $N(0,1)$), and put $\Lambda_\sigma(t)=\Lambda(t)+t^2\sigma^2/2$; $\Phi$ is the standard normal distribution function. For $T\in\mathbb R$ let $\kappa_T$ be the probability law with density proportional to $d\mapsto f(\tfrac{T+d}2)f(\tfrac{T-d}2)$ (the conditional law of $S'-S''$ given $S'+S''=T$ for independent smoothed sums), $F_T$ its distribution function and $Q_T(u)=\inf\{x:u\le F_T(x)\}$. There are $C,\varepsilon_q,\beta>0$ and $N_3\ge1$ such that for every finite $\iota$ with $n\ge N_3$, $0<\sigma\le1$ with $\sigma^{-1}\le e^{\beta n}$, $|T|\le\tfrac{t_1}4\,2n$ and $|u|<\varepsilon_q\,2n$
--
--   $$\Big|Q_T\Big(\Phi\Big(\frac u{\sqrt{\Lambda''(0)+\sigma^2}\sqrt{2n}}\Big)\Big)-u\Big|\leC\Big(1+\frac{u^2}{2n}+\frac{T^2}{2n}\Big).$$
--
--   Role: The node bound $|\tilde U_{jk}-\tilde V_{jk}|<C_1 2^{-j}(\tilde U_{jk}^2+U_{jk}^2)+C_2$ for $k<2^{\alpha2^j}$ in the proof of Theorem 1A.
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Section 3, proof of Theorem 1A, p. 40 (node bounds under |U_jk|, |U~_jk| < eps 2^j, k < 2^(alpha 2^j))

import Mathlib

namespace EthierKurtz

theorem kmt_smoothed_conditional_quantile_bound :
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
                                    ∃ (C : ℝ) (εq : ℝ) (β : ℝ) (N3 : ℝ),
                                      (0 : ℝ) < C ∧
                                        (0 : ℝ) < εq ∧
                                          (0 : ℝ) < β ∧
                                            (1 : ℝ) ≤ N3 ∧
                                              ∀ (ι : Type) [inst : Fintype ι] (σ T : ℝ),
                                                (0 : ℝ) < σ →
                                                  σ ≤ (1 : ℝ) →
                                                    N3 ≤ ↑(Fintype.card ι) →
                                                      σ⁻¹ ≤ Real.exp (β * ↑(Fintype.card ι)) →
                                                        |T| ≤ t1 / (4 : ℝ) * ((2 : ℝ) * ↑(Fintype.card ι)) →
                                                          ∀ (u : ℝ),
                                                            |u| < εq * ((2 : ℝ) * ↑(Fintype.card ι)) →
                                                              |InfSet.sInf
                                                                      {x : ℝ |
                                                                        (ProbabilityTheory.cdf
                                                                                (ProbabilityTheory.gaussianReal (0 : ℝ)
                                                                                  (1 : NNReal)))
                                                                            (u /
                                                                              (√(iteratedDeriv (2 : ℕ)
                                                                                      (ProbabilityTheory.cgf
                                                                                        (fun (x : ℝ) => x) G)
                                                                                      (0 : ℝ) +
                                                                                    σ ^ (2 : ℕ)) *
                                                                                √((2 : ℝ) * ↑(Fintype.card ι)))) ≤
                                                                          (ProbabilityTheory.cdf
                                                                                ((ProbabilityTheory.Kernel.withDensity
                                                                                    (ProbabilityTheory.Kernel.const ℝ
                                                                                      MeasureTheory.MeasureSpace.volume)
                                                                                    fun (T d : ℝ) =>
                                                                                    ENNReal.ofReal
                                                                                          (∫ (y : ℝ),
                                                                                            ProbabilityTheory.gaussianPDFReal
                                                                                              (0 : ℝ)
                                                                                              (Real.toNNReal
                                                                                                (↑(Fintype.card ι) *
                                                                                                  σ ^ (2 : ℕ)))
                                                                                              ((T + d) / (2 : ℝ) -
                                                                                                y) ∂MeasureTheory.Measure.map
                                                                                              (fun (p : ι → ℝ) =>
                                                                                                ∑ i : ι, p i)
                                                                                              (MeasureTheory.Measure.pi
                                                                                                fun (x : ι) => G)) *
                                                                                        ENNReal.ofReal
                                                                                          (∫ (y : ℝ),
                                                                                            ProbabilityTheory.gaussianPDFReal
                                                                                              (0 : ℝ)
                                                                                              (Real.toNNReal
                                                                                                (↑(Fintype.card ι) *
                                                                                                  σ ^ (2 : ℕ)))
                                                                                              ((T - d) / (2 : ℝ) -
                                                                                                y) ∂MeasureTheory.Measure.map
                                                                                              (fun (p : ι → ℝ) =>
                                                                                                ∑ i : ι, p i)
                                                                                              (MeasureTheory.Measure.pi
                                                                                                fun (x : ι) => G)) *
                                                                                      (∫⁻ (d : ℝ),
                                                                                          ENNReal.ofReal
                                                                                              (∫ (y : ℝ),
                                                                                                ProbabilityTheory.gaussianPDFReal
                                                                                                  (0 : ℝ)
                                                                                                  (Real.toNNReal
                                                                                                    (↑(Fintype.card ι) *
                                                                                                      σ ^ (2 : ℕ)))
                                                                                                  ((T + d) / (2 : ℝ) -
                                                                                                    y) ∂MeasureTheory.Measure.map
                                                                                                  (fun (p : ι → ℝ) =>
                                                                                                    ∑ i : ι, p i)
                                                                                                  (MeasureTheory.Measure.pi
                                                                                                    fun (x : ι) => G)) *
                                                                                            ENNReal.ofReal
                                                                                              (∫ (y : ℝ),
                                                                                                ProbabilityTheory.gaussianPDFReal
                                                                                                  (0 : ℝ)
                                                                                                  (Real.toNNReal
                                                                                                    (↑(Fintype.card ι) *
                                                                                                      σ ^ (2 : ℕ)))
                                                                                                  ((T - d) / (2 : ℝ) -
                                                                                                    y) ∂MeasureTheory.Measure.map
                                                                                                  (fun (p : ι → ℝ) =>
                                                                                                    ∑ i : ι, p i)
                                                                                                  (MeasureTheory.Measure.pi
                                                                                                    fun (x : ι) => G)))⁻¹)
                                                                                  T))
                                                                            x} -
                                                                    u| ≤
                                                                C *
                                                                  ((1 : ℝ) + u ^ (2 : ℕ) / ((2 : ℝ) * ↑(Fintype.card ι)) +
                                                                    T ^ (2 : ℕ) / ((2 : ℝ) * ↑(Fintype.card ι))) := by sorry

end EthierKurtz
