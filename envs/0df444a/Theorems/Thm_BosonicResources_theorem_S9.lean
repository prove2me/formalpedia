-- Prove2me | Theorems.Thm_BosonicResources_theorem_S9
-- name    : BosonicResources.theorem_S9
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:38:35.026232+00:00
-- url     : https://prove2.me/theorems/37d569e7-88ea-4eac-885d-dbff581cad13
-- title:
--   Theorem S9 (upper bound): heterodyne tomography of passive Gaussian states with $O(n^3/\varepsilon^2)$ copies
-- statement:
--   An $n$-mode Gaussian state is a state of $n$ bosonic modes whose Wigner function is a Gaussian distribution. A Gaussian state is *passive* if its density operator is block diagonal in the total photon number, i.e. $\langle u\rvert\rho\lvert v\rangle=0$ whenever the Fock states $\lvert u\rangle,\lvert v\rangle$ have different total photon numbers. *Heterodyne detection* of one copy of a state $\rho$ produces an outcome $\beta\in\mathbb R^{2n}$ whose probability density is the Husimi function $Q_\rho(\beta)=(2\pi)^{-n}\langle\alpha(\beta)\rvert\rho\lvert\alpha(\beta)\rangle$, where $\lvert\alpha(\beta)\rangle$ is the coherent state with quadrature means $\beta$ (quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$); in the paper's terms it is the Gaussian measurement with seed covariance $\tfrac12 I$. The trace distance is $D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$.
--
--   There is a universal constant $C>0$ such that for every $n\ge1$ and every $\varepsilon\in(0,1)$ there exist an integer $N$ with
--
--   $$
--   N\ \le\ C\,\frac{n^{3}}{\varepsilon^{2}}
--   $$
--
--   and a measurable estimator $\hat\rho$ from $(\mathbb R^{2n})^{N}$ to density operators with the following property: for every $n$-mode passive Gaussian state $\rho$, if $Y_1,\dots,Y_N$ are the outcomes of independent heterodyne detections of $N$ copies of $\rho$, then $D_{\mathrm{tr}}(\hat\rho(Y_1,\dots,Y_N),\rho)\le\varepsilon$ with probability at least $2/3$.
--
--   Combined with the lower bound of Theorem 2 for classical measurements, this identifies $\Theta(n^{3}/\varepsilon^{2})$ as the sample complexity of learning passive Gaussian states with Gaussian measurements, with no dependence at all on the energy. It is the part of Theorem 6 stating that the classical-measurement bound $\Theta(n^{3}/\varepsilon^{2})$ is attained.
--
--   **Formalization Note** This is the upper-bound half of Theorem S9; the converse half is `theorem_2`. No energy promise is made. The protocol ($N$ and the estimator) is chosen before the state. The estimator is deterministic, as in the paper's protocol and in the published `BosonicLearn.heterodyneSuccess`, with which the statement is written; the heterodyne outcome law there is the measure with Husimi density (its identification with the Gaussian measurement with seed $\tfrac12 I$ is the separate statement `heterodyne_gaussian_measurement`), and passivity is the published `BosonicLearn.IsPassive`.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, App. D.2, Theorem S9

import Mathlib
import Definitions.Def_BosonicLearn_heterodyneSuccess
import Definitions.Def_BosonicLearn_IsPassive
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Theorem S9 (Heterodyne tomography of passive Gaussian states with `O(n³/ε²)` copies).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Theorem S9 (App. D.2): "The sample complexity of learning n-mode passive Gaussian states via Gaussian
operations is Θ(n³/ε²). In particular, heterodyne tomography performed on O(n³/ε²) copies of an unknown passive
Gaussian state learns the state to trace-distance accuracy ε with probability at least 2/3. Conversely, any protocol
restricted to Gaussian operations requires Ω(n³/ε²) copies." Preceding text: "with no dependence at all on the
energy".

There is a universal `C > 0` such that for every `n ≥ 1` and `ε ∈ (0, 1)` there are `N ≤ C n³/ε²` and a measurable
estimator of `N` independent heterodyne outcomes that learns every `n`-mode passive Gaussian state to trace distance
`ε` with probability at least `2/3`.

**Formalization Note.** This is the upper-bound half; the converse half is `theorem_2`. No energy promise is made.
The protocol (`N` and the estimator) is chosen before the state. The estimator is deterministic, as in the paper's
protocol and in the published `BosonicLearn.heterodyneSuccess`. -/
theorem theorem_S9 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) ^ 3 / ε ^ 2) ∧
        ∃ est : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → State (Occupation (Fin n)),
          Measurable est ∧
          ∀ ρ : State (Occupation (Fin n)), IsPassive ρ →
            ENNReal.ofReal (2 / 3) ≤ heterodyneSuccess N est ρ ε := by sorry

end BosonicResources
