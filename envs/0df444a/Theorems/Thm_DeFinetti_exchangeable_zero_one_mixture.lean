-- Prove2me | Theorems.Thm_DeFinetti_exchangeable_zero_one_mixture
-- name    : DeFinetti.exchangeable_zero_one_mixture
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:52:17.131668+00:00
-- url     : https://prove2.me/theorems/13ce1e41-cde5-4930-800c-92a2003c2717
-- title:
--   de Finetti's theorem: an infinite exchangeable $0$–$1$ sequence is a unique mixture of Bernoulli trials
-- statement:
--   This is de Finetti's theorem for exchangeable sequences of $0$–$1$ random variables: every such sequence is a mixture of i.i.d. Bernoulli sequences.
--
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and let $X_1, X_2, X_3, \dots$ be random variables on it that take only the values $0$ and $1$. The finite family $X_1,\dots,X_n$ is called *exchangeable* if for every permutation $(k_1,\dots,k_n)$ of $(1,\dots,n)$ the random vector $(X_{k_1},\dots,X_{k_n})$ has the same $n$-dimensional distribution as $(X_1,\dots,X_n)$; the infinite sequence $(X_k)$ is *exchangeable* if $X_1,\dots,X_n$ are exchangeable for every $n$. Write $S_n = X_1 + \dots + X_n$.
--
--   **Theorem (de Finetti).** If the infinite sequence $(X_k)$ is exchangeable, then there is a probability distribution $F$ concentrated on the interval $[0,1]$ such that for all integers $0 \le k \le n$:
--
--   1. the probability that the first $k$ variables equal $1$ and the next $n-k$ equal $0$ is
--   $$
--   \mathbb P\{X_1 = 1,\dots,X_k = 1,\ X_{k+1} = 0,\dots,X_n = 0\} = \int_0^1 \theta^{k}(1-\theta)^{n-k}\, F\{d\theta\};
--   $$
--   2. the number of successes among the first $n$ trials has the mixed binomial law
--   $$
--   \mathbb P\{S_n = k\} = \binom{n}{k}\int_0^1 \theta^{k}(1-\theta)^{n-k}\, F\{d\theta\}.
--   $$
--
--   Moreover $F$ is **unique**: if $G$ is any probability distribution concentrated on $[0,1]$ such that identity 1 holds with $G$ in place of $F$ for all $0 \le k \le n$, then $G = F$. (Taking $k = n$ shows that $G$ and $F$ have the same moments $\int_0^1 \theta^n$, and a distribution on the compact interval $[0,1]$ is determined by its moments — the uniqueness half of the Hausdorff moment problem.)
--
--   In words: an infinite exchangeable $0$–$1$ sequence behaves as if a success probability $\theta$ were first drawn at random from $F$ and the trials were then independent Bernoulli$(\theta)$ trials. This representation is the foundation of the subjectivist (Bayesian) interpretation of probability, where $F$ plays the role of a prior distribution, and it is the prototype of the representation theorems for symmetric measures (Hewitt–Savage) and for exchangeable sequences in general Borel spaces (Ryll-Nardzewski). The hypothesis that the sequence is infinite cannot be dropped: finite exchangeable families need not be mixtures of i.i.d. sequences.
--
--   **Formalization Note** The sequence is indexed from $0$: `X i` stands for $X_{i+1}$, so the event in (1) is $\{X_i = 1 \text{ for } i<k,\ X_i = 0 \text{ for } k \le i < n\}$ and $S_n$ is `∑ i ∈ Finset.range n, X i`. The variables are real-valued, measurable, and take the value $0$ or $1$ at every point. Exchangeability is stated directly: for every $n$ and every `σ : Equiv.Perm (Fin n)`, the push-forward of $\mathbb P$ under $\omega \mapsto (X_{\sigma(i)}(\omega))_{i<n}$ equals the push-forward under $\omega \mapsto (X_i(\omega))_{i<n}$. The mixing distribution $F$ is a probability measure on $\mathbb R$ with $F(\mathbb R \setminus [0,1]) = 0$, so the integrands are bounded $F$-almost everywhere and the Bochner integrals are genuine. Probabilities are converted to real numbers with `ENNReal.toReal`. The case $n = 0$ is included and reduces to $1 = F([0,1])$. Uniqueness is stated among probability measures $G$ on $\mathbb R$ with $G(\mathbb R \setminus [0,1]) = 0$, assuming of $G$ only identity 1 for all $k \le n$, and concludes the equality of measures `G = F`; this is equivalent to uniqueness among Borel probability measures on $[0,1]$.
-- source:
--   W. Feller, An Introduction to Probability Theory and Its Applications, Vol. II, 2nd ed., Wiley, 1971, Chapter VII (Laws of Large Numbers. Applications in Analysis), Section 4 (exchangeable variables): the definition of exchangeable variables and the theorem attributed there to de Finetti (probabilities of the pattern X_1 = ... = X_k = 1, X_{k+1} = ... = X_n = 0 and of S_n = k as mixtures over a distribution F concentrated on [0,1]). Original: B. de Finetti, Funzione caratteristica di un fenomeno aleatorio, Atti della R. Accademia Nazionale dei Lincei, Memorie, Classe di Scienze Fisiche, Matematiche e Naturali, Ser. 6, Vol. 4 (1931), 251-299. General form: E. Hewitt and L. J. Savage, Symmetric measures on Cartesian products, Trans. Amer. Math. Soc. 80 (1955), 470-501. Uniqueness of F: F is determined by its moments, by the uniqueness half of the Hausdorff moment problem (Feller, Vol. II, Chapter VII, Section 3).

import Mathlib

open MeasureTheory ProbabilityTheory

namespace DeFinetti

/-- **de Finetti's theorem** for exchangeable `0`-`1` sequences (Feller, Vol. II, §VII.4).
Let `X 0, X 1, …` be random variables on a probability space `(Ω, P)` taking only the values
`0` and `1`, and suppose they are exchangeable: for every `n` and every permutation `σ` of
`{0, …, n-1}`, the vector `(X (σ 0), …, X (σ (n-1)))` has the same law as `(X 0, …, X (n-1))`.
Then there is a unique probability distribution `F` on `ℝ` concentrated on `[0, 1]` such that
for all `k ≤ n`
`P{X 0 = 1, …, X (k-1) = 1, X k = 0, …, X (n-1) = 0} = ∫ θ^k (1-θ)^(n-k) dF(θ)`.
Moreover `P{X 0 + ⋯ + X (n-1) = k} = (n choose k) ∫ θ^k (1-θ)^(n-k) dF(θ)`.
Uniqueness: any probability distribution `G` on `ℝ` concentrated on `[0, 1]` satisfying the
first identity for all `k ≤ n` equals `F`. -/
theorem exchangeable_zero_one_mixture {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hXmeas : ∀ i, Measurable (X i))
    (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hexch : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      P.map (fun ω (i : Fin n) => X (σ i) ω) = P.map (fun ω (i : Fin n) => X i ω)) :
    ∃ F : Measure ℝ, IsProbabilityMeasure F ∧ F (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      (∀ n k : ℕ, k ≤ n →
        (P {ω | ∀ i < n, X i ω = if i < k then 1 else 0}).toReal
            = ∫ θ, θ ^ k * (1 - θ) ^ (n - k) ∂F ∧
        (P {ω | ∑ i ∈ Finset.range n, X i ω = k}).toReal
            = (n.choose k : ℝ) * ∫ θ, θ ^ k * (1 - θ) ^ (n - k) ∂F) ∧
      ∀ G : Measure ℝ, IsProbabilityMeasure G → G (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        (∀ n k : ℕ, k ≤ n →
          (P {ω | ∀ i < n, X i ω = if i < k then 1 else 0}).toReal
            = ∫ θ, θ ^ k * (1 - θ) ^ (n - k) ∂G) →
        G = F := by sorry

end DeFinetti
