-- Prove2me | Theorems.Thm_BosonicResources_heterodyne_gaussian_measurement
-- name    : BosonicResources.heterodyne_gaussian_measurement
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T05:50:50.967593+00:00
-- url     : https://prove2.me/theorems/18d821d4-f90e-41e1-832a-b7c5fff900ae
-- title:
--   Heterodyne detection is the Gaussian measurement with seed covariance $\tfrac12 I$
-- statement:
--   Consider an $n$-mode bosonic system with Fock space $\ell^2(\mathbb N^n)$ and quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$, with the vacuum covariance equal to $\tfrac12 I$. A **Gaussian (general-dyne) measurement with seed covariance $V$** is a POVM with outcomes $\xi\in\mathbb R^{2n}$ whose elements are $(2\pi)^{-n}\rho(\xi,V)\,d\xi$, where $\rho(\xi,V)$ is the Gaussian state with mean $\xi$ and covariance $V$. The **heterodyne law** of a density operator $\rho$ is the probability measure on $\mathbb R^{2n}$ with Lebesgue density given by the Husimi function
--
--   $$
--   Q_\rho(\beta)=(2\pi)^{-n}\,\langle\alpha(\beta)|\rho|\alpha(\beta)\rangle,\qquad \alpha_j=\frac{\beta_{x_j}+i\,\beta_{p_j}}{\sqrt2},
--   $$
--
--   where $|\alpha\rangle$ is the coherent state of amplitude $\alpha$.
--
--   For every $n$:
--
--   1. there exists a POVM on the $n$-mode Fock space, with outcomes in $\mathbb R^{2n}$, that is a Gaussian measurement with seed covariance $V=\tfrac12 I$;
--   2. for every such POVM $P$ and every density operator $\rho$ on the $n$-mode Fock space (Gaussian or not), the Born outcome law of $P$ on $\rho$ equals the heterodyne law of $\rho$:
--
--   $$
--   \Pr_P[\xi\in B\mid\rho]=\int_B Q_\rho(\beta)\,d\beta\qquad\text{for every Borel set }B\subseteq\mathbb R^{2n}.
--   $$
--
--   This identifies the two descriptions of heterodyne detection that appear in the mission: the Husimi-density law, in which the heterodyne upper bounds (Theorem S9) are stated, and the Gaussian measurement with vacuum seed, in which the heterodyne lower bound (Theorem 4) and the class of classical measurements are stated. It is what makes the heterodyne protocol of Theorem S9 a classical measurement in the sense of Theorem 2.
--
--   **Formalization Note** The heterodyne law is the published `BosonicLearn.heterodyneLaw` (a measure with density `husimiQ` with respect to Lebesgue measure) and the Gaussian measurement is `BosonicResources.IsGaussianMeasurement P ((1/2) • 1)`. The first part asserts that the predicate is satisfiable, so the second part is not vacuous. The outcome law is the `law` field of the POVM, which on density operators is given by the Born rule.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 2 (heterodyne measurements, V = (1/2) I_{2n}); Fig. 2(a); App. D.2, Theorem S9

import Mathlib
import Definitions.Def_BosonicLearn_heterodyneLaw
import Definitions.Def_BosonicResources_IsGaussianMeasurement
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Heterodyne detection is the Gaussian measurement with seed covariance `½I`.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, §2: "Two examples of Gaussian measurements that are commonly used in quantum optics experiments are heterodyne
measurements (V = ½ I_{2n}) and homodyne measurements"; Fig. 2(a): "Heterodyne measurements …, whose seeds are always
the vacuum state"; Theorem S9: "heterodyne tomography … learns the state", used in Theorem 6 as the classical
measurement that attains `Θ(n³/ε²)`.

For every number of modes `n`:
1. there is a POVM on the `n`-mode Fock space with outcomes in `ℝ²ⁿ` that is a Gaussian measurement with seed covariance
   `½I` (the seed is the vacuum, the elements are `(2π)^{-n}` times coherent-state projectors);
2. for every such POVM `P` and every density operator `ρ` (Gaussian or not), the Born outcome law of `P` on `ρ` is the
   heterodyne law of the published `BosonicLearn.heterodyneLaw`, the measure on `ℝ²ⁿ` with Lebesgue density
   `Q_ρ(β) = (2π)^{-n} ⟨α(β)|ρ|α(β)⟩` (Husimi function; `α_j = (β_{q,j} + i β_{p,j})/√2`).

**Formalization Note.** The mission uses two published or new descriptions of heterodyne detection: the Husimi-density
law (in `heterodyneSuccess`, used for the heterodyne upper bound `theorem_S9`) and the Gaussian
measurement with `V = ½I` (in `theorem_4` and, through `gaussian_scheme_classical`, in the class of classical
measurements). This statement identifies them, so that the heterodyne protocol of `theorem_S9` is a classical
measurement in the sense of `theorem_2`. -/
theorem heterodyne_gaussian_measurement (n : ℕ) :
    (∃ P : FockPOVM (Occupation (Fin n)) (EuclideanSpace ℝ (Fin n ⊕ Fin n)),
        IsGaussianMeasurement P ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))) ∧
      ∀ P : FockPOVM (Occupation (Fin n)) (EuclideanSpace ℝ (Fin n ⊕ Fin n)),
        IsGaussianMeasurement P ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) →
        ∀ ρ : State (Occupation (Fin n)), P.law ρ.coefficients = heterodyneLaw ρ.coefficients := by sorry

end BosonicResources
