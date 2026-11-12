-- Prove2me | Theorems.Thm_DKFAsymptotics_lemma1
-- name    : DKFAsymptotics.lemma1
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-15T20:52:55.031233+00:00
-- url     : https://prove2.me/theorems/4696feaf-8bc8-4f3f-aaec-7bcb16b9294c
-- title:
--   Lemma 1 — DKF equation and asymptotic concentration
-- statement:
--   Fix a positive finite state dimension and a stationary linear Gaussian model with transition density $\eta_d(z;Ay,\Gamma)$ and stationary density $p(z)=\eta_d(z;0,S)$, where $\Gamma,S$ are symmetric positive definite and $S=ASA^\top+\Gamma$.
--
--   For sequences of Gaussian densities $s'_n=\eta_d(\cdot;a_n,V_n)$ and $u'_n=\eta_d(\cdot;b_n,U_n)$ with positive-definite covariances, define
--
--   $$G_n=AV_nA^\top+\Gamma,\quad T_n=(U_n^{-1}+G_n^{-1}-S^{-1})^{-1},\quad c_n=T_n(U_n^{-1}b_n+G_n^{-1}Aa_n).$$
--
--   At every index where the precision matrix is invertible and $T_n$ is positive definite, the normalized density update is well defined, is a probability density, and equals $\eta_d(z;c_n,T_n)$ at every $z$.
--
--   Furthermore, for every probability measure $P$ and state $b$, if $s'_n\Rightarrow P$ and $u'_n\Rightarrow\delta_b$, then the update is eventually valid with positive-definite covariance, is eventually a Gaussian probability density, and converges weakly to $\delta_b$. The measure $P$ may be degenerate; no invertibility of $G_n^{-1}-S^{-1}$ is assumed.
-- source:
--   M. C. Burkhart, D. M. Brandman, B. Franco, L. R. Hochberg and M. T. Harrison, The Discriminative Kalman Filter for Bayesian Filtering with Nonlinear and Nongaussian Observation Models, Neural Computation 32(5), 969–1017 (2020), doi:10.1162/neco_a_01275; https://burkh4rt.github.io/pubs/Burkhart-et-al-2020-Neural-Comput.pdf; Appendix B, Lemma 1, pp. 1007–1010.

import Definitions.Def_DKFAsymptotics_Assumptions

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics

theorem lemma1 {d : ℕ} [NeZero d] (M : Model d)
    (a b' : ℕ+ → State d) (V U : ℕ+ → Covariance d)
    (hV : ∀ n, (V n).PosDef) (hU : ∀ n, (U n).PosDef)
    (P : ProbabilityMeasure (State d)) (b : State d) :
    (∀ n, ValidStep M ⟨a n, V n⟩ ⟨b' n, U n⟩ →
      UpdateDefined M (gaussianPDF (a n) (V n)) (gaussianPDF (b' n) (U n)) ∧
      (∀ z, updateDensity M (gaussianPDF (a n) (V n)) (gaussianPDF (b' n) (U n)) z =
        gaussianPDF (dkfStep M ⟨a n, V n⟩ ⟨b' n, U n⟩).mean
          (dkfStep M ⟨a n, V n⟩ ⟨b' n, U n⟩).covariance z) ∧
      IsPDF (updateDensity M (gaussianPDF (a n) (V n)) (gaussianPDF (b' n) (U n)))) ∧
    (Weakly (fun n => gaussianPDF (a n) (V n)) P →
      Weakly (fun n => gaussianPDF (b' n) (U n)) (Measure.dirac b) →
      (∀ᶠ n in atTop,
        ValidStep M ⟨a n, V n⟩ ⟨b' n, U n⟩ ∧
        UpdateDefined M (gaussianPDF (a n) (V n)) (gaussianPDF (b' n) (U n)) ∧
        IsGaussianPDF (updateDensity M (gaussianPDF (a n) (V n))
          (gaussianPDF (b' n) (U n)))) ∧
      Weakly (fun n => updateDensity M (gaussianPDF (a n) (V n))
        (gaussianPDF (b' n) (U n))) (Measure.dirac b)) := by sorry

end DKFAsymptotics
