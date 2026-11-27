-- Prove2me | Theorems.Thm_BosonicResources_main_results
-- name    : BosonicResources.main_results
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:40:29.23529+00:00
-- url     : https://prove2.me/theorems/cfc0e081-daaa-4fb6-b978-f4d41890b522
-- title:
--   Main results (Theorems 2–5, 7): lower bounds for classical, arbitrary and heterodyne measurements, pure-state upper bound, non-adaptive single-copy Gaussian schemes
-- statement:
--   The task is to learn an unknown $n$-mode Gaussian state $\rho(\mu,\Sigma)$ to trace distance $\varepsilon$ with probability at least $2/3$ from $N$ copies. This theorem collects the main sample-complexity bounds of the paper, sorted by the class of measurements the learner may use:
--
--   $$
--   \begin{aligned}
--   &\text{classical measurements, passive states (Thm. 2):} && N=\Omega\!\Big(\frac{n^{3}}{\varepsilon^{2}}\Big),\\
--   &\text{arbitrary measurements (Thm. 3):} && N=\Omega\!\Big(\frac{n^{2}}{\varepsilon^{2}}\Big),\qquad N=\Omega\!\Big(\frac{n^{2}}{\varepsilon^{2}\log(n/\varepsilon)}\Big)\ \text{for pure states},\\
--   &\text{heterodyne measurements (Thm. 4):} && N=\Omega\!\Big(\frac{\bar E^{2}n^{3}}{\varepsilon^{2}}\Big),\\
--   &\text{pure states, Gaussian measurements (Thm. 5):} && N=O\!\Big(\frac{n^{2}}{\varepsilon^{2}}+\big(n+\log\log\log\bar E\big)\log\log\bar E\Big),\\
--   &\text{one mode, non-adaptive single-copy Gaussian measurements (Thm. 7):} && N=\Omega\!\Big(\frac{\bar E}{\varepsilon^{2}}\Big),\qquad N=O\!\Big(\frac{\bar E\log\bar E}{\varepsilon^{2}}\Big).
--   \end{aligned}
--   $$
--
--   **Setting.** An $n$-mode bosonic system has quadrature operators ordered $(\hat x_1,\dots,\hat x_n,\hat p_1,\dots,\hat p_n)$. For $\mu\in\mathbb R^{2n}$ and a real $2n\times2n$ matrix $\Sigma$, $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu$ and covariance matrix $\Sigma$, in the convention where the vacuum has covariance $\tfrac12 I$. A state is *pure* if it is a rank-one projector. A Gaussian state is *passive* if its density operator is block diagonal in the total photon number, i.e. $\langle u\rvert\rho\lvert v\rangle=0$ whenever the Fock states $\lvert u\rangle,\lvert v\rangle$ have different total photon numbers. The energy promise is $\|\Sigma\|_{\mathrm{op}}\le\bar E$, and $\log$ is the natural logarithm. An estimate $\hat\rho$ of $\rho$ is *$\varepsilon$-accurate* if $D_{\mathrm{tr}}(\hat\rho,\rho)=\tfrac12\|\hat\rho-\rho\|_1\le\varepsilon$, and a protocol *learns $\rho$ to trace distance $\varepsilon$* if, run on $\rho^{\otimes N}$, it outputs an $\varepsilon$-accurate estimate with probability at least $2/3$. Four kinds of protocols appear.
--
--   - A *learner on $N$ copies* is a POVM on the $N$-copy Hilbert space, possibly entangled across the copies, whose outcome is the estimate $\hat\rho$, a density operator. It is *classical* if all of its elements have non-negative Wigner functions: for every measurable set $B$ of outcomes, the POVM element $E(B)$ has a Wigner function $W_{E(B)}\ge 0$, that is, a bounded measurable function $W_{E(B)}\ge0$ on the $N$-copy phase space $(\mathbb R^{2n})^{N}$ with $\langle u\rvert E(B)\lvert v\rangle=(2\pi)^{nN}\int W_{E(B)}(r)\,W_{\lvert v\rangle\langle u\rvert}(r)\,dr$ for all Fock states $u,v$ of the $N$ copies (here $W_{\lvert v\rangle\langle u\rvert}$ is the Wigner function of the Fock matrix unit).
--   - A *Gaussian (general-dyne) measurement with seed covariance $V$* is the POVM on one copy with outcomes $\xi\in\mathbb R^{2n}$ and elements $(2\pi)^{-n}\rho(\xi,V)\,d\xi$, the displaced copies of a Gaussian seed state with covariance $V$; *heterodyne detection* is the case $V=\tfrac12 I$. An *adaptive single-copy Gaussian scheme* measures the $N$ copies one at a time by Gaussian measurements, where the seed used on the $t$-th copy may depend on the outcomes of the first $t-1$ measurements, and then applies an *estimator*, a possibly randomized map from the $N$ outcomes to a density operator $\hat\rho$.
--   - A *heterodyne protocol* is such a scheme in which every copy is measured by heterodyne detection.
--   - A *non-adaptive single-copy Gaussian scheme* consists of shared randomness $\omega$, drawn once from a probability measure on a measurable space $\Lambda$ independently of the state, and, for each $\omega$ and each copy $t$, a Gaussian measurement (with a seed that may depend on $\omega$ and $t$) applied to copy $t$ alone; given $\omega$ the $N$ outcomes are independent, and no measurement depends on the outcome of another. Its estimator is a possibly randomized map from $\omega$ and the $N$ outcomes to a density operator.
--
--   **Statement.** The following five claims hold, each with its own universal constants.
--
--   1. *(Theorem 2: classical measurements.)* There are $c>0$, $E_0\in\mathbb R$ and $n_0\in\mathbb N$ such that for every $n\ge n_0$, every $\varepsilon\in(0,1/36]$ and every $N$: if a learner on $N$ copies that is a classical POVM learns to trace distance $\varepsilon$ every passive $n$-mode Gaussian state $\rho(\mu,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le E_0$, then $N\ge c\,n^{3}/\varepsilon^{2}$.
--   2. *(Theorem 3: arbitrary measurements.)* There are $c>0$, $\varepsilon_0>0$, $E_0\in\mathbb R$ and $n_0\in\mathbb N$ such that for every $n\ge n_0$, every $\varepsilon\in(0,\varepsilon_0)$, every $N$ and every learner $P$ on $N$ copies: (a) if $P$ learns to trace distance $\varepsilon$ every zero-mean $n$-mode Gaussian state $\rho(0,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le E_0$, then $N\ge c\,n^{2}/\varepsilon^{2}$; (b) if $P$ learns to trace distance $\varepsilon$ every *pure* zero-mean $n$-mode Gaussian state $\rho(0,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le E_0$, then $N\ge c\,n^{2}/\big(\varepsilon^{2}\log(n/\varepsilon)\big)$.
--   3. *(Theorem 4: heterodyne measurements.)* There are $c>0$ and $n_0\in\mathbb N$ such that for every $n\ge n_0$, every $\varepsilon\in(0,0.005)$, every $\bar E>1$ and every $N$: if some heterodyne protocol on $N$ copies learns to trace distance $\varepsilon$ every zero-mean $n$-mode Gaussian state $\rho(0,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le\bar E$, then $N\ge c\,\bar E^{2}n^{3}/\varepsilon^{2}$.
--   4. *(Theorem 5: pure states.)* There is $C>0$ such that for every $n\ge1$, every $\varepsilon\in(0,1)$ and every $\bar E\ge16$ there exist an integer $N\le C\big(n^{2}/\varepsilon^{2}+(n+\log\log\log\bar E)\log\log\bar E\big)$ and an adaptive single-copy Gaussian scheme on $N$ copies with an estimator that learn to trace distance $\varepsilon$ every pure $n$-mode Gaussian state $\rho(\mu,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le\bar E$.
--   5. *(Theorem 7: one mode, non-adaptive single-copy Gaussian measurements.)* Let $n=1$. (a) There are $c>0$, $\varepsilon_0>0$ and $E_0\in\mathbb R$ such that for every $\bar E\ge E_0$, every $\varepsilon\in(0,\varepsilon_0)$ and every $N$: if some non-adaptive single-copy Gaussian scheme on $N$ copies (with any space $\Lambda$ of shared randomness) and some estimator learn to trace distance $\varepsilon$ every zero-mean one-mode Gaussian state $\rho(0,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le\bar E$, then $N\ge c\,\bar E/\varepsilon^{2}$. (b) There is $C>0$ such that for every $\bar E\ge2$ and every $\varepsilon\in(0,1)$ there exist an integer $N\le C\,\bar E\log\bar E/\varepsilon^{2}$, a non-adaptive single-copy Gaussian scheme on $N$ copies and an estimator that learn to trace distance $\varepsilon$ every one-mode Gaussian state $\rho(\mu,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le\bar E$.
--
--   Claim 1 shows that the adaptive Gaussian protocol of [BMEM25], which uses $\widetilde O(n^{3}/\varepsilon^{2})$ copies, is nearly optimal among classical measurements, which include all Gaussian measurements. Claims 2 and 4 give the nearly tight bound $\widetilde\Theta(n^{2}/\varepsilon^{2})$ for pure Gaussian states, attained by Gaussian measurements. Claim 3 matches the heterodyne upper bound $O(\bar E^{2}n^{3}/\varepsilon^{2})$ of [BMEM25]. Claim 5 shows that single-copy Gaussian schemes need adaptivity to reach the nearly energy-independent sample complexity of [BMEM25].
--
--   **Formalization Note** The Lean statement is the conjunction of five clauses, and each clause is identical to the statement of the corresponding milestone of this mission (Theorems 2, 3, 4, 5 and 7), where its reading is discussed in detail. $\Omega$ and $O$ are universal constants. The lower bounds are asymptotic in $n$ (threshold $n_0$) and hold for small $\varepsilon$, with the explicit ranges of the appendix where it gives them (Theorem S3 for claim 1, Theorem S7 for claim 3); where the paper writes $\|\Sigma\|_{\mathrm{op}}=O(1)$ they hold on the sub-class $\|\Sigma\|_{\mathrm{op}}\le E_0$. Claim 4 is stated for $\bar E\ge16$, where the iterated logarithms are positive, and claim 5(b) for $\bar E\ge2$. $\|\Sigma\|_{\mathrm{op}}\le\bar E$ is written as positive semidefiniteness of $\bar E\cdot I-\Sigma$. In every upper bound the protocol is chosen before the state. Lean objects: `BosonicLearn.collectiveSuccess` and `IsClassical` (claims 1–2), `BosonicLearn.AdaptiveScheme` with `IsGaussianMeasurement` / `IsGaussianScheme` and `BosonicLearn.successProb` (claims 3–4), `NonadaptiveGaussianScheme` and `nonadaptiveSuccess` (claim 5), `BosonicLearn.IsPassive`, `IsPure`. The upper bound of Theorem 6 for passive states, which rests on the passive random purification channel, is not part of this statement or of this mission.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 3.2, Theorems 2, 3 and 4; Sec. 3.3, Theorem 5, Eq. (4); Sec. 3.4, Theorem 7; Table 1. Precise forms: App. C.1, Theorem S3; App. C.2, Theorems S4 and S5; App. C.3, Theorem S7; App. D.1, Theorem S8; App. E, Theorems S12 and S13

import Mathlib
import Definitions.Def_BosonicLearn_collectiveSuccess
import Definitions.Def_BosonicLearn_successProb
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicLearn_IsPassive
import Definitions.Def_BosonicResources_IsPure
import Definitions.Def_BosonicResources_IsClassical
import Definitions.Def_BosonicResources_IsGaussianMeasurement
import Definitions.Def_BosonicResources_NonadaptiveGaussianScheme
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Main results: lower bounds, the pure-state upper bound, and non-adaptive single-copy Gaussian schemes
(Theorems 2, 3, 4, 5 and 7).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Sec. 3.2–3.4 (see also Table 1). The task is to learn an `n`-mode Gaussian state
`ρ(μ, Σ)` to trace distance `ε` with probability at least `2/3`. The paper states:

* Theorem 2: "N = Ω(n³/ε²) copies are necessary to learn an n-mode Gaussian states ρ(μ,Σ) to ε trace distance
  closeness with probability 2/3 using classical measurements, even with the promise that ‖Σ‖_op = O(1) and ρ is
  passive. A POVM is classical if all of its elements have non-negative Wigner functions."
* Theorem 3: "N = Ω(n²/ε²) copies are necessary to learn an n-mode Gaussian states ρ(μ,Σ) to ε trace distance
  closeness with probability 2/3 using any POVM measurements, even with the promise that ‖Σ‖_op = O(1) and ρ has zero
  mean. Furthermore, even if ρ is promised to be pure, N = Ω̃(n²/ε²) = Ω(n²/(ε² log(n/ε))) copies are still
  necessary."
* Theorem 4: "N = Ω(Ē²n³/ε²) copies are necessary to learn an n-mode Gaussian state ρ(μ,Σ) with the promise that
  ‖Σ‖_op ≤ Ē to ε trace distance closeness with probability 2/3 using heterodyne measurements."
* Theorem 5: "A number of N = Õ(n²/ε²) = O(n²/ε² + (n + log log log Ē) log log Ē) copies are sufficient to learn an
  n-mode Gaussian state ρ(μ,Σ) to ε trace distance closeness with probability 2/3 given the promise that ρ is pure
  and ‖Σ‖_op ≤ Ē. Moreover, this can be achieved by Gaussian measurements."
* Theorem 7: "Focus on one-mode systems and non-adaptive, non-entangling, Gaussian measurements. Then N = Ω(Ē/ε²)
  copies are necessary to learn a Gaussian state ρ(μ,Σ) to ε trace distance closeness with probability 2/3 given the
  promise that ‖Σ‖_op ≤ Ē. Furthermore, there exists a scheme that achieves this using N = O(Ē log Ē/ε²) samples."

The statement is the conjunction of five claims:
1. (Theorem 2) a classical POVM on `N` copies that learns every passive Gaussian state with `‖Σ‖_op ≤ E₀` has
   `N ≥ c n³/ε²`;
2. (Theorem 3) a POVM on `N` copies that learns every zero-mean Gaussian state with `‖Σ‖_op ≤ E₀` has `N ≥ c n²/ε²`,
   and one that learns every pure zero-mean Gaussian state with `‖Σ‖_op ≤ E₀` has `N ≥ c n²/(ε² log(n/ε))`;
3. (Theorem 4) a heterodyne protocol on `N` copies that learns every zero-mean Gaussian state with `‖Σ‖_op ≤ Ē` has
   `N ≥ c Ē² n³/ε²`;
4. (Theorem 5) some adaptive single-copy Gaussian scheme with `N ≤ C (n²/ε² + (n + log log log Ē) log log Ē)` copies
   learns every pure Gaussian state with `‖Σ‖_op ≤ Ē`;
5. (Theorem 7) for one mode, a non-adaptive single-copy Gaussian scheme on `N` copies that learns every zero-mean
   Gaussian state with `‖Σ‖_op ≤ Ē` has `N ≥ c Ē/ε²`, and some such scheme with `N ≤ C Ē log Ē/ε²` copies learns every
   Gaussian state with `‖Σ‖_op ≤ Ē`.

**Formalization Note.** Each of the five conjuncts is, word for word, the statement of the corresponding milestone
(`theorem_2`, `theorem_3`, `theorem_4`, `theorem_5`, `theorem_7`), where the reading of each theorem is explained in
detail; the constants are separate for each conjunct. `Ω`, `O` are universal constants. Lower bounds are asymptotic in
`n` (threshold `n₀`) and hold for small `ε` (`ε ≤ 1/36` in claim 1 as in Theorem S3, `ε < 0.005` in claim 3 as in
Theorem S7, `ε < ε₀` otherwise); where the paper says `‖Σ‖_op = O(1)` they hold on the sub-class `‖Σ‖_op ≤ E₀`.
Claim 4 is stated for `Ē ≥ 16`, where the iterated logarithms are positive, claim 3 for `Ē > 1` and the upper bound of
claim 5 for `Ē ≥ 2`. `‖Σ‖_op ≤ E` is `E·I − Σ ⪰ 0`. In claims 1–2 the learner is a POVM on all `N` copies whose
outcome is the estimate (`collectiveSuccess`), which covers every measurement followed by classical post-processing; in
claims 3–4 it is a single-copy scheme (`AdaptiveScheme`) of Gaussian measurements with a Markov-kernel estimator
(heterodyne: seed covariance `½I` in every round); in claim 5 it is a `NonadaptiveGaussianScheme` with shared
randomness. In every upper bound the protocol is chosen before the state. The upper bound of Theorem 6, which rests on
the passive random purification channel, is not part of this statement. -/
theorem main_results :
    -- 1. Theorem 2 (classical measurements, passive states): N ≥ c n³/ε²
    (∃ c : ℝ, 0 < c ∧ ∃ E₀ : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 36 →
       ∀ (N : ℕ) (P : FockPOVM (Fin N → Occupation (Fin n)) (State (Occupation (Fin n)))),
         IsClassical P →
         (∀ (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
             (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
           IsPassive ρ → IsGaussianState ρ μ S →
           (E₀ • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
           ENNReal.ofReal (2 / 3) ≤ collectiveSuccess P ρ ε) →
         c * ((n : ℝ) ^ 3 / ε ^ 2) ≤ N) ∧
    -- 2. Theorem 3 (arbitrary measurements): N ≥ c n²/ε², and N ≥ c n²/(ε² log(n/ε)) for pure states
    (∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ E₀ : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
       ∀ (N : ℕ) (P : FockPOVM (Fin N → Occupation (Fin n)) (State (Occupation (Fin n)))),
         ((∀ (ρ : State (Occupation (Fin n))) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
             IsGaussianState ρ 0 S →
             (E₀ • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
             ENNReal.ofReal (2 / 3) ≤ collectiveSuccess P ρ ε) →
           c * ((n : ℝ) ^ 2 / ε ^ 2) ≤ N) ∧
         ((∀ (ρ : State (Occupation (Fin n))) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
             IsPure ρ → IsGaussianState ρ 0 S →
             (E₀ • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
             ENNReal.ofReal (2 / 3) ≤ collectiveSuccess P ρ ε) →
           c * ((n : ℝ) ^ 2 / (ε ^ 2 * Real.log ((n : ℝ) / ε))) ≤ N)) ∧
    -- 3. Theorem 4 (heterodyne measurements): N ≥ c Ē² n³/ε²
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < 0.005 → ∀ E : ℝ, 1 < E →
       ∀ (N : ℕ) (Sch : AdaptiveScheme n N (EuclideanSpace ℝ (Fin n ⊕ Fin n)))
         (est : Kernel (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) (State (Occupation (Fin n)))),
         IsMarkovKernel est →
         (∀ (t : Fin N) (x : Fin t → EuclideanSpace ℝ (Fin n ⊕ Fin n)),
           IsGaussianMeasurement (Sch.povm t x)
             ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))) →
         (∀ (ρ : State (Occupation (Fin n))) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
           IsGaussianState ρ 0 S →
           (E • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
           ENNReal.ofReal (2 / 3) ≤ successProb Sch est ρ.coefficients ε) →
         c * (E ^ 2 * (n : ℝ) ^ 3 / ε ^ 2) ≤ N) ∧
    -- 4. Theorem 5 (pure states, adaptive single-copy Gaussian measurements): N ≤ C (n²/ε² + (n + log log log Ē) log log Ē)
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ E : ℝ, 16 ≤ E →
       ∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) ^ 2 / ε ^ 2 +
           ((n : ℝ) + Real.log (Real.log (Real.log E))) * Real.log (Real.log E)) ∧
         ∃ Sch : AdaptiveScheme n N (EuclideanSpace ℝ (Fin n ⊕ Fin n)), IsGaussianScheme Sch ∧
           ∃ est : Kernel (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) (State (Occupation (Fin n))),
             IsMarkovKernel est ∧
             ∀ (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
                 (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
               IsPure ρ → IsGaussianState ρ μ S →
               (E • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
               ENNReal.ofReal (2 / 3) ≤ successProb Sch est ρ.coefficients ε) ∧
    -- 5. Theorem 7 (one mode, non-adaptive single-copy Gaussian measurements): N ≥ c Ē/ε² and N ≤ C Ē log Ē/ε²
    ((∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ E₀ : ℝ, ∀ E : ℝ, E₀ ≤ E → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
       ∀ (N : ℕ) (Λ : Type) [MeasurableSpace Λ] (Sch : NonadaptiveGaussianScheme 1 N Λ)
         (est : Kernel (Λ × (Fin N → EuclideanSpace ℝ (Fin 1 ⊕ Fin 1))) (State (Occupation (Fin 1)))),
         IsMarkovKernel est →
         (∀ (ρ : State (Occupation (Fin 1))) (S : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ),
           IsGaussianState ρ 0 S →
           (E • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) - S).PosSemidef →
           ENNReal.ofReal (2 / 3) ≤ nonadaptiveSuccess Sch est ρ.coefficients ε) →
         c * (E / ε ^ 2) ≤ N) ∧
     (∃ C : ℝ, 0 < C ∧ ∀ E : ℝ, 2 ≤ E → ∀ ε : ℝ, 0 < ε → ε < 1 →
       ∃ N : ℕ, (N : ℝ) ≤ C * (E * Real.log E / ε ^ 2) ∧
         ∃ (Λ : Type) (_ : MeasurableSpace Λ) (Sch : NonadaptiveGaussianScheme 1 N Λ)
           (est : Kernel (Λ × (Fin N → EuclideanSpace ℝ (Fin 1 ⊕ Fin 1))) (State (Occupation (Fin 1)))),
           IsMarkovKernel est ∧
           ∀ (ρ : State (Occupation (Fin 1))) (μ : Fin 1 ⊕ Fin 1 → ℝ)
               (S : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ),
             IsGaussianState ρ μ S →
             (E • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) - S).PosSemidef →
             ENNReal.ofReal (2 / 3) ≤ nonadaptiveSuccess Sch est ρ.coefficients ε)) := by sorry

end BosonicResources
