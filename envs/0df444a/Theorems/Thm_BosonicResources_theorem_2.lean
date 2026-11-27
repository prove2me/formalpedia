-- Prove2me | Theorems.Thm_BosonicResources_theorem_2
-- name    : BosonicResources.theorem_2
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:31:51.253624+00:00
-- url     : https://prove2.me/theorems/b15604e7-90d6-4c68-a943-bc07addc8224
-- title:
--   Theorem 2: $\Omega(n^3/\varepsilon^2)$ copies are necessary with classical measurements
-- statement:
--   Throughout, $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix; quadratures are ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$ and the vacuum has covariance $\tfrac12 I$. A Gaussian state is *passive* if its density operator is block diagonal in the total photon number, i.e. $\langle u\rvert\rho\lvert v\rangle=0$ whenever the Fock states $\lvert u\rangle,\lvert v\rangle$ have different total photon numbers.
--
--   A *learner on $N$ copies* is a POVM on the $N$-copy Hilbert space, possibly entangled across the copies, whose outcome is the estimate $\hat\rho$, a density operator. It *learns $\rho$ to trace distance $\varepsilon$* if, measured on $\rho^{\otimes N}$, its outcome satisfies $D_{\mathrm{tr}}(\hat\rho,\rho)=\tfrac12\|\hat\rho-\rho\|_1\le\varepsilon$ with probability at least $2/3$. A POVM on $N$ copies is *classical* if all of its elements have non-negative Wigner functions: for every measurable set $B$ of outcomes, the POVM element $E(B)$ has a Wigner function $W_{E(B)}\ge 0$, that is, a bounded measurable function $W_{E(B)}\ge0$ on the $N$-copy phase space $(\mathbb R^{2n})^{N}$ with $\langle u\rvert E(B)\lvert v\rangle=(2\pi)^{nN}\int W_{E(B)}(r)\,W_{\lvert v\rangle\langle u\rvert}(r)\,dr$ for all Fock states $u,v$ of the $N$ copies (here $W_{\lvert v\rangle\langle u\rvert}$ is the Wigner function of the Fock matrix unit).
--
--   There are universal constants $c>0$, $E_0\in\mathbb R$ and $n_0\in\mathbb N$ such that the following holds for every $n\ge n_0$, every $\varepsilon\in(0,1/36]$ and every $N$. Let $P$ be a learner on $N$ copies that is a classical POVM. If $P$ learns to trace distance $\varepsilon$ every passive $n$-mode Gaussian state $\rho(\mu,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le E_0$, then
--
--   $$
--   N\ \ge\ c\,\frac{n^{3}}{\varepsilon^{2}} .
--   $$
--
--   Since Gaussian measurements are classical measurements, the theorem shows that the adaptive Gaussian protocol of [BMEM25], which uses $\widetilde O(n^{3}/\varepsilon^{2})$ copies, is nearly optimal among all Gaussian measurement schemes. It is also the classical-measurement half of the non-Gaussian advantage of Theorem 6.
--
--   **Formalization Note** $\Omega(\cdot)$ is a universal constant $c$ and a threshold $n_0$ (the proof needs $n>9$). The range $\varepsilon\le1/36$ is that of the precise form, Theorem S3. $\|\Sigma\|_{\mathrm{op}}=O(1)$ is a universal bound $E_0$; $\|\Sigma\|_{\mathrm{op}}\le E_0$ is written as positive semidefiniteness of $E_0\cdot I-\Sigma$ ($\Sigma$ is symmetric positive definite). Any classical measurement followed by classical post-processing is again a classical POVM with outcomes in the state space, so the "outcome is the estimate" form (`BosonicLearn.collectiveSuccess`) covers every such scheme. Passivity is the published `BosonicLearn.IsPassive` (passive states have zero mean) and classicality is `IsClassical`.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 3.2, Theorem 2; App. C.1, Theorem S3

import Mathlib
import Definitions.Def_BosonicLearn_collectiveSuccess
import Definitions.Def_BosonicLearn_IsPassive
import Definitions.Def_BosonicResources_IsClassical
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Theorem 2 (Lower bound with classical measurements).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Theorem 2: "N = Ω(n³/ε²) copies are necessary to learn an n-mode Gaussian states ρ(µ,Σ) to ε trace distance
closeness with probability 2/3 using classical measurements, even with the promise that ‖Σ‖_op = O(1) and ρ is
passive. A POVM is classical if all of its elements have non-negative Wigner functions." Precise form, Theorem S3
(App. C.1): "to trace distance precision ε ≤ 1/36 … using general (possibly adaptive, ancilla-assisted, multi-copy)
Gaussian measurements … The above theorem actually applies for any (collective) POVM whose elements all have
non-negative Wigner functions".

There are constants `c > 0`, `E₀` and `n₀` such that for every `n ≥ n₀`, every `ε ∈ (0, 1/36]`, every `N` and every
classical POVM on `N` copies (entangled across copies) whose outcome is the estimate: if every passive Gaussian state
with `‖Σ‖_op ≤ E₀` is learned to trace distance `ε` with probability at least `2/3`, then `N ≥ c n³/ε²`.

**Formalization Note.** `Ω(·)` is a universal constant `c` and a threshold `n₀` (the proof needs `n > 9`).
`‖Σ‖_op = O(1)` is a universal bound `E₀`; `‖Σ‖_op ≤ E₀` is written `E₀·I − Σ ⪰ 0` (Σ is symmetric positive
definite). Any classical measurement followed by classical post-processing is again a classical POVM with outcomes
in the state space, so the "outcome is the estimate" form covers every such scheme. -/
theorem theorem_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ E₀ : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 36 →
      ∀ (N : ℕ) (P : FockPOVM (Fin N → Occupation (Fin n)) (State (Occupation (Fin n)))),
        IsClassical P →
        (∀ (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
            (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
          IsPassive ρ → IsGaussianState ρ μ S →
          (E₀ • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
          ENNReal.ofReal (2 / 3) ≤ collectiveSuccess P ρ ε) →
        c * ((n : ℝ) ^ 3 / ε ^ 2) ≤ N := by sorry

end BosonicResources
