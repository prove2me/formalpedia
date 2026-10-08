-- Prove2me | Theorems.Thm_CohenLeeSongLP_StochCentralPath_classical_step_probability_bound
-- name    : CohenLeeSongLP.StochCentralPath.classical_step_probability_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:42:44.658987+00:00
-- url     : https://prove2.me/theorems/8eb846b5-d0bb-44f8-8b7d-ac4c0c973ff8
-- title:
--   Lemma 4.14 — Assumption 4.1 always holds during Main, and ClassicalStep happens with probability at most $10/n^2$ per step
-- statement:
--   Lemma 4.14 of the paper reads: "During the Main algorithm, Assumption 4.1 is always satisfied. Furthermore, the ClassicalStep happens with probability $O(\frac{1}{n^2})$ each step."
--
--   Precisely: let $n\ge10$ and let $A\in\mathbb R^{d\times n}$ have full row rank. Run the iteration of Main (Algorithm 2, lines 7–17) with $\epsilon=\frac1{40000\log n}$, $\epsilon_{\mathrm{mp}}=\frac1{40000}$, $k=\frac{1000\epsilon\sqrt n\log^2n}{\epsilon_{\mathrm{mp}}}$, $\lambda=40\log n$ and $t_j=(1-\frac{\epsilon}{3\sqrt n})^j$, from positive $x^0,s^0$ with $x^0s^0\approx_{1/\lambda}1$. The data structure is any family of functions $U_j$ of the history $(x^0,s^0,\dots,x^j,s^j)$ returning $\widetilde v$ with $x^j/s^j\approx_{\epsilon_{\mathrm{mp}}}\widetilde v$ whenever $x^j,s^j>0$; ClassicalStep is any family of functions $C_j$ of the history returning positive $(x',s')$ with $\Phi_\lambda(x's'/t_{j+1}-1)\le n^3$ whenever $x^j,s^j>0$ and $x^js^j\approx_{0.1}t_j$. Both are measurable and neither sees the coins of iteration $j$. Let $\mathbb P$ be the law of the trajectory (Ionescu-Tulcea), whose transition from a history is the law of one iteration of Main. Then for every iteration $j\ge0$:
--
--   1. (i)–(ii) almost surely, Assumption 4.1 holds for the input $(x^j,s^j,t_j,\widetilde v,\delta_\mu,k,\epsilon,\epsilon_{\mathrm{mp}})$ of iteration $j$'s StochasticStep, in particular $x^js^j\approx_{0.1}t_j$ and $\|\delta_\mu\|_2\le\epsilon t_j$;
--   2. (iv) almost surely, the success event of iteration $j$'s resampling loop has positive probability, so the step is a genuine conditioned law;
--   3. (iii) the probability that iteration $j$ invokes ClassicalStep is at most $10/n^2$:
--   $$\mathbb P\big(\text{ClassicalStep is used in iteration } j\big)\le\frac{10}{n^2}.$$
--
--   This is the probabilistic core of the running-time analysis: the paper's per-iteration cost bound (Lemma 4.16) multiplies the $\widetilde O(n^{2.5})$ cost of ClassicalStep by this probability.
--
--   **Formalization Note** The paper writes $O(1/n^2)$; its proof gives $10/n^2$ ($\mathbf E[\Phi^{(j)}]\le 10n$ and Markov's inequality at $n^3$), and that constant is stated. Assumption 4.1 is used with the non-strict $\epsilon\le1/(40000\log n)$, which Main's choice of $\epsilon$ attains. The conclusions are stated for every $j\in\mathbb N$ instead of only while $t>\delta^2/(32n^3)$. The trajectory kernels are a parameter, required to be Markov and equal pointwise to the step law of Main.
-- source:
--   Cohen, Lee and Song, Solving Linear Programs in the Current Matrix Multiplication Time, J. ACM 68(1), Article 3 (2021), p. 3:20, Lemma 4.14 (O(1/n²) instantiated as 10/n² from its proof); p. 3:10, Algorithm 2

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_Main

open MeasureTheory ProbabilityTheory

namespace CohenLeeSongLP.StochCentralPath

/-- Lemma 4.14 (p. 3:20). Run Main (Algorithm 2, lines 7–17) with its parameters
`ε = 1/(40000 log n)`, `ε_mp = 1/40000`, `k = 1000ε√n log² n/ε_mp`, `λ = 40 log n`, on a
full-row-rank `A`, from positive `x⁰, s⁰` with `x⁰s⁰ ≈_{1/λ} 1` and `t₀ = 1`. The update oracle
`U` returns, from the history, a `ṽ` with `x/s ≈_{ε_mp} ṽ` for the current positive iterate;
the ClassicalStep oracle `C` returns, from the history, a positive pair `(x', s')` with
`Φ_λ(x's'/t_{j+1} − 1) ≤ n³` whenever the current iterate is positive with `xs ≈_{0.1} t_j`.
The trajectory law is built by Ionescu-Tulcea from kernels equal to the step law of Main.
Then for every iteration `j`:
(i)–(ii) almost surely, Assumption 4.1 holds for the input of iteration `j`'s StochasticStep;
(iv) almost surely, the success event of iteration `j`'s resampling loop has positive probability;
(iii) the probability that iteration `j` invokes ClassicalStep is at most `10/n²`. -/
theorem classical_step_probability_bound {n d : ℕ} (hn : 10 ≤ n)
    (A : Matrix (Fin d) (Fin n) ℝ) (hA : A.rank = d)
    (x0 s0 : Fin n → ℝ) (hx0 : ∀ i, 0 < x0 i) (hs0 : ∀ i, 0 < s0 i)
    (hinit : ApproxScalar (1 / lam n) (fun i => x0 i * s0 i) 1)
    (U : (j : ℕ) → ((i : Finset.Iic j) → State n) → (Fin n → ℝ))
    (hUmeas : ∀ j, Measurable (U j))
    (hU : ∀ j (h : (i : Finset.Iic j) → State n),
      (∀ i, 0 < (current h).1 i) → (∀ i, 0 < (current h).2.1 i) →
      ApproxVec epsMp (fun i => (current h).1 i / (current h).2.1 i) (U j h))
    (C : (j : ℕ) → ((i : Finset.Iic j) → State n) → (Fin n → ℝ) × (Fin n → ℝ))
    (hCmeas : ∀ j, Measurable (C j))
    (hC : ∀ j (h : (i : Finset.Iic j) → State n),
      (∀ i, 0 < (current h).1 i) → (∀ i, 0 < (current h).2.1 i) →
      ApproxScalar 0.1 (fun i => (current h).1 i * (current h).2.1 i) (tSeq n j) →
      (∀ i, 0 < (C j h).1 i) ∧ (∀ i, 0 < (C j h).2 i) ∧
      potential (lam n) (fun i => (C j h).1 i * (C j h).2 i / tSeq n (j + 1) - 1) ≤ (n : ℝ) ^ 3)
    (κ : (j : ℕ) → ProbabilityTheory.Kernel ((i : Finset.Iic j) → State n) (State n))
    [∀ j, IsMarkovKernel (κ j)]
    (hκ : ∀ j h, κ j h = mainStepLaw A U C j h) (j : ℕ) :
    (∀ᵐ (ω : (k : ℕ) → State n) ∂(ProbabilityTheory.Kernel.trajMeasure (Measure.dirac (x0, s0, false)) κ),
      Assumption41 (ω j).1 (ω j).2.1 (tSeq n j) (U j (fun i => ω i))
        (direction (lam n) (eps n) (tSeq n j) (tSeq n (j + 1)) (ω j).1 (ω j).2.1)
        (kSampMain n) (eps n) epsMp) ∧
    (∀ᵐ (ω : (k : ℕ) → State n) ∂(ProbabilityTheory.Kernel.trajMeasure (Measure.dirac (x0, s0, false)) κ),
      0 < sampleLaw (kSampMain n)
        (direction (lam n) (eps n) (tSeq n j) (tSeq n (j + 1)) (ω j).1 (ω j).2.1)
        (successEvent A (ω j).1 (ω j).2.1 (U j (fun i => ω i)))) ∧
    ProbabilityTheory.Kernel.trajMeasure (Measure.dirac (x0, s0, false)) κ
        {ω : (k : ℕ) → State n | (ω (j + 1)).2.2 = true} ≤ ENNReal.ofReal (10 / (n : ℝ) ^ 2) := by sorry

end CohenLeeSongLP.StochCentralPath
