-- Prove2me | Theorems.Thm_EthierKurtz_tilted_local_limit_smoothed_sum_density
-- name    : EthierKurtz.tilted_local_limit_smoothed_sum_density
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:25:16.296466+00:00
-- url     : https://prove2.me/theorems/54f3d185-1998-4722-94c4-a9b1913bb877
-- title:
--   Local limit theorem for the conjugate (tilted) smoothed sum
-- statement:
--   Let $G$ be a probability law on $\mathbb R$ with $\int e^{ax}\,dG(x)<\infty$ for $|a|\le a_0$, and suppose $G=p\,N(m,v)+(1-p)F_2$ with $0<p\le1$, $v>0$ and $F_2$ a probability law (a Gaussian component). Let $\Lambda=\log R$ be the cumulant generating function of $G$, $R(t)=\int e^{tx}dG$. Let $0<t_1$ with $2t_1<a_0$ such that $\tfrac12\le\Lambda''(t)\le2$ and $\int e^{tx}\,dN(m,v)\big/R(t)\ge\tfrac12$ for $|t|\le t_1$. For a finite index set $\iota$ with $n=|\iota|$ and $\sigma>0$ let $f(a)=E\,\varphi_{n\sigma^2}(a-\sum_{i\in\iota}X_i)$ ($X_i$ i.i.d. $G$, $\varphi_V$ the $N(0,V)$ density) be the density of the smoothed sum $\sum_i(X_i+\sigma\eta_i)$ ($\eta_i$ i.i.d. $N(0,1)$), and put $\Lambda_\sigma(t)=\Lambda(t)+t^2\sigma^2/2$; $\Phi$ is the standard normal distribution function. There are $C>0$ and $0<\kappa'\le1$ such that for every finite $\iota$ with $n\ge2$, $|t|\le t_1$, $0<\sigma\le1$ and $a\in\mathbb R$
--
--   $$\Big|f(a)-R(t)^ne^{t^2n\sigma^2/2}e^{-ta}\varphi_{n(\Lambda''(t)+\sigma^2)}\big(a-tn\sigma^2-n\Lambda'(t)\big)\Big|\le R(t)^ne^{t^2n\sigma^2/2}e^{-ta}\Big(\frac Cn+\frac{C(1-\kappa')^{n-1}}\sigma\Big).$$
--
--   Role: The conjugate-distribution formula (3.1) combined with the local limit estimate of Lemma A and (3.2), giving the display at the top of p. 40 in the proof of Lemma 2.
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Section 3, Lemma 2 and its proof, pp. 38-40, formulas (3.1)-(3.2) and Lemma A (Petrov's local limit theorem, reference [4] there)

import Mathlib

namespace EthierKurtz

theorem tilted_local_limit_smoothed_sum_density :
    ∀ {G : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure G] {a0 : ℝ},
      (∀ (a : ℝ), |a| ≤ a0 → MeasureTheory.Integrable (fun (x : ℝ) => Real.exp (a * x)) G) →
        ∀ (p m : ℝ) (v : NNReal) (F2 : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure F2],
          (0 : ℝ) < p →
            p ≤ (1 : ℝ) →
              (0 : NNReal) < v →
                G = ENNReal.ofReal p • ProbabilityTheory.gaussianReal m v + ENNReal.ofReal ((1 : ℝ) - p) • F2 →
                  ∀ {t1 : ℝ},
                    (0 : ℝ) < t1 →
                      (2 : ℝ) * t1 < a0 →
                        (∀ (t : ℝ),
                            |t| ≤ t1 →
                              (1 / 2 : ℝ) ≤ iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ∧
                                iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ≤ (2 : ℝ)) →
                          (∀ (t : ℝ),
                              |t| ≤ t1 →
                                (1 / 2 : ℝ) ≤
                                  ProbabilityTheory.mgf (fun (x : ℝ) => x) (ProbabilityTheory.gaussianReal m v) t /
                                    ProbabilityTheory.mgf (fun (x : ℝ) => x) G t) →
                            ∃ (C : ℝ) (κ' : ℝ),
                              (0 : ℝ) < C ∧
                                (0 : ℝ) < κ' ∧
                                  κ' ≤ (1 : ℝ) ∧
                                    ∀ (ι : Type) [inst : Fintype ι] (t σ a : ℝ),
                                      |t| ≤ t1 →
                                        (0 : ℝ) < σ →
                                          σ ≤ (1 : ℝ) →
                                            (2 : ℕ) ≤ Fintype.card ι →
                                              |∫ (y : ℝ),
                                                      ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                        (Real.toNNReal (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                        (a -
                                                          y) ∂MeasureTheory.Measure.map (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                        (MeasureTheory.Measure.pi fun (x : ι) => G) -
                                                    ProbabilityTheory.mgf (fun (x : ℝ) => x) G t ^ Fintype.card ι *
                                                          Real.exp
                                                            (t ^ (2 : ℕ) * (↑(Fintype.card ι) * σ ^ (2 : ℕ)) / (2 : ℝ)) *
                                                        Real.exp (-(t * a)) *
                                                      ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                        (Real.toNNReal
                                                          (↑(Fintype.card ι) *
                                                            (iteratedDeriv (2 : ℕ)
                                                                (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t +
                                                              σ ^ (2 : ℕ))))
                                                        (a - t * (↑(Fintype.card ι) * σ ^ (2 : ℕ)) -
                                                          ↑(Fintype.card ι) *
                                                            deriv (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t)| ≤
                                                ProbabilityTheory.mgf (fun (x : ℝ) => x) G t ^ Fintype.card ι *
                                                      Real.exp (t ^ (2 : ℕ) * (↑(Fintype.card ι) * σ ^ (2 : ℕ)) / (2 : ℝ)) *
                                                    Real.exp (-(t * a)) *
                                                  (C / ↑(Fintype.card ι) +
                                                    C * ((1 : ℝ) - κ') ^ (Fintype.card ι - (1 : ℕ)) / σ) := by sorry

end EthierKurtz
