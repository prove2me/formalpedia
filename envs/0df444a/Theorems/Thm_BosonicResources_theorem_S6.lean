-- Prove2me | Theorems.Thm_BosonicResources_theorem_S6
-- name    : BosonicResources.theorem_S6
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:37:55.205896+00:00
-- url     : https://prove2.me/theorems/36690b94-298e-4167-92a6-add7aefc9767
-- title:
--   Theorem S6: $\Omega(n^2/\varepsilon^2)$ copies are necessary for passive Gaussian states with arbitrary measurements
-- statement:
--   Throughout, $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix; quadratures are ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$ and the vacuum has covariance $\tfrac12 I$. A Gaussian state is *passive* if its density operator is block diagonal in the total photon number, i.e. $\langle u\rvert\rho\lvert v\rangle=0$ whenever the Fock states $\lvert u\rangle,\lvert v\rangle$ have different total photon numbers.
--
--   A *learner on $N$ copies* is a POVM on the $N$-copy Hilbert space, possibly entangled across the copies, whose outcome is the estimate $\hat\rho$, a density operator. It *learns $\rho$ to trace distance $\varepsilon$* if, measured on $\rho^{\otimes N}$, its outcome satisfies $D_{\mathrm{tr}}(\hat\rho,\rho)=\tfrac12\|\hat\rho-\rho\|_1\le\varepsilon$ with probability at least $2/3$.
--
--   There are universal constants $c>0$, $\varepsilon_0>0$, $E_0\in\mathbb R$ and $n_0\in\mathbb N$ such that the following holds for every $n\ge n_0$, every $\varepsilon\in(0,\varepsilon_0)$, every $N$ and every learner $P$ on $N$ copies. If $P$ learns to trace distance $\varepsilon$ every passive $n$-mode Gaussian state $\rho(\mu,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le E_0$, then
--
--   $$
--   N\ \ge\ c\,\frac{n^{2}}{\varepsilon^{2}} .
--   $$
--
--   This is the lower bound that the upper bound $\widetilde O(n^{2}/\varepsilon^{2})$ of Theorem 6 "nearly matches". In contrast to the general lower bound of Theorem 3, it holds on the class of passive Gaussian states, for arbitrary (collective, non-Gaussian) measurements.
--
--   **Formalization Note** The bound is stated on the sub-class $\|\Sigma\|_{\mathrm{op}}\le E_0$ (a universal constant), which the ensemble of the proof, Eq. (S97), satisfies; this is what makes it a lower bound for the task of Theorem 6 at every energy $\bar E\ge E_0$, and it implies the bound for the class of all passive Gaussian states. $\Omega(\cdot)$ is a universal constant with thresholds $n_0$ and $\varepsilon_0$ (the proof assumes "$\varepsilon$ is upper bounded by a sufficiently small constant"). $\|\Sigma\|_{\mathrm{op}}\le E_0$ is encoded as positive semidefiniteness of $E_0\cdot I-\Sigma$. Passive states have zero mean, so the printed "zero-mean passive" is the published `BosonicLearn.IsPassive`; the learner is a POVM whose outcome is the estimate (`BosonicLearn.collectiveSuccess`).
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, App. C.2.2, Theorem S6 (ensemble in Eq. (S97)); used in Sec. 3.3, Theorem 6

import Mathlib
import Definitions.Def_BosonicLearn_collectiveSuccess
import Definitions.Def_BosonicLearn_IsPassive
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Theorem S6 (Lower bound for passive Gaussian states with arbitrary measurements).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Theorem S6 (App. C.2.2): "For any algorithm that learns an unknown zero-mean passive n-mode Gaussian state
ρ(0,Σ) to trace distance precision ε with probability at least 2/3 using any POVM measurements, the number of copies
must satisfy N = Ω(n²/ε²)." Proof: "we assume ε is upper bounded by a sufficiently small constant"; the ensemble,
Eq. (S97), has `Σ_a = ((1 + 1/n)/2) I + (ε/2n) diag(U_a U_aᵀ, U_a U_aᵀ)`. Used in Theorem 6: "which nearly matches the
lower bound of N = Ω(n²/ε²)".

There are constants `c > 0`, `ε₀ > 0`, `E₀` and `n₀` such that for every `n ≥ n₀`, `ε ∈ (0, ε₀)`, every `N` and every
POVM on `N` copies (entangled across copies) whose outcome is the estimate: if every passive Gaussian state with
`‖Σ‖_op ≤ E₀` is learned to trace distance `ε` with probability at least `2/3`, then `N ≥ c n²/ε²`.

**Formalization Note.** The bound is stated on the sub-class `‖Σ‖_op ≤ E₀` (a universal constant), which the
ensemble of the proof satisfies; this is what makes it a lower bound for the task of Theorem 6 at every energy
`Ē ≥ E₀`, and it implies the bound for the class of all passive Gaussian states. `‖Σ‖_op ≤ E₀` is `E₀·I − Σ ⪰ 0`.
Passive states have zero mean. -/
theorem theorem_S6 :
    ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ E₀ : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (N : ℕ) (P : FockPOVM (Fin N → Occupation (Fin n)) (State (Occupation (Fin n)))),
        (∀ (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
            (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
          IsPassive ρ → IsGaussianState ρ μ S →
          (E₀ • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
          ENNReal.ofReal (2 / 3) ≤ collectiveSuccess P ρ ε) →
        c * ((n : ℝ) ^ 2 / ε ^ 2) ≤ N := by sorry

end BosonicResources
