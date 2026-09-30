-- Prove2me | Theorems.Thm_ComputationalLearning_vc_sample_bound
-- name    : ComputationalLearning.vc_sample_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:14:04.953989+00:00
-- url     : https://prove2.me/theorems/0c71be0d-6a86-4cc0-8900-e7b4e38b2631
-- title:
--   Theorems 3.3-3.4: a consistent hypothesis from a class of VC dimension d is PAC, with failure ≤ 2Φ_d(2m)2^(−εm/2) and explicit m
-- statement:
--   **Theorem 3.3.** Let $C$ be any concept class of VC dimension $d$. Let $L$ be any algorithm that takes as input a set $S$ of $m$ labeled examples of a concept in $C$, and produces as output a concept $h \in C$ that is consistent with $S$. Then $L$ is a PAC learning algorithm for $C$ provided it is given a random sample of $m$ examples from $EX(c, D)$, where $m \ge c_0\big(\tfrac{1}{\epsilon}\log\tfrac{1}{\delta} + \tfrac{d}{\epsilon}\log\tfrac{1}{\epsilon}\big)$ for some constant $c_0 > 0$. **Theorem 3.4** is the same with a hypothesis class $H$ of VC dimension $d$ in place of $C$.
--
--   Formally, for a class $H$ of measurable hypotheses with $\mathrm{vcDim}(H) \le d$, a measurable target $c$ for which $H$ is well-behaved (the double-sample event is null-measurable), a distribution $D$, $0 < \epsilon < 1$, $0 < \delta < 1$ and $m \ge 8/\epsilon$: (1) the probability that the points of a random sample of $m$ examples fail to form an $\epsilon$-net for the error regions $\{c \,\Delta\, h : h \in H\}$ is at most $2\Phi_d(2m)2^{-\epsilon m/2}$ (the bound of p. 61: $\Pr[A] \le 2\Pr[B]$, and $\Pr[B] \le |\Pi_{\Delta(c)}(S)|\,2^{-\epsilon m/2}$ by the random partition of the double sample); (2) hence every algorithm outputting a hypothesis in $H$ consistent with its sample has error greater than $\epsilon$ with probability at most $2\Phi_d(2m)2^{-\epsilon m/2}$; (3) if moreover $m \ge (4/\epsilon)\log_2(2/\delta)$ and $m \ge (8d/\epsilon)\log_2(13/\epsilon)$, that probability is at most $\delta$ (the explicit constants of Blumer, Ehrenfeucht, Haussler and Warmuth, which instantiate the book's $c_0$); (4) consequently, if $H$ is nonempty, every class $C \subseteq H$ for whose targets $H$ is well-behaved is PAC learnable using $H$. For $H = \emptyset$ no algorithm outputs hypotheses in $H$, so (4) needs $H$ nonempty; the book's classes always are.
--
--   **Why well-behavedness.** The proof bounds the probability that the sample is not an $\epsilon$-net by twice the probability of a double-sample event, and bounds the latter by averaging over the random swaps of the two samples. Both steps integrate over the double sample, so the event must be measurable. Blumer, Ehrenfeucht, Haussler and Warmuth (J. ACM 36, 1989) state the theorem for well-behaved classes for this reason. Without the condition the theorem is false. Take $X = \omega_1$ with the countable–cocountable $\sigma$-algebra and $D$ the probability measure that is $1$ on co-countable sets and $0$ on countable ones. Let $H$ be the final segments $(\alpha, \omega_1)$ together with the empty concept; it has VC dimension $1$ and consists of measurable concepts. For the target $c = \emptyset$, every finite sample misses $(\max S, \omega_1)$, which has weight $1$. So no sample is an $\epsilon$-net, and the consistent learner that outputs $(\max S, \omega_1)$ has error $1$ with probability $1$. The double-sample event fails to be measurable there, because $\{(x, y) : x < y\}$ is not measurable for the product $\sigma$-algebra.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §3.5 pp. 57-62, Theorem 3.3 with its proof (ε-nets, the double sample and the random partition) and Theorem 3.4

import Definitions.Def_ComputationalLearning_VC

open MeasureTheory

namespace ComputationalLearning

/-- **Theorems 3.3 and 3.4** (pp. 61–62). Let `H` be a class of VC dimension at most `d` and `L`
any algorithm that outputs a hypothesis `h ∈ H` consistent with its sample of `m` labeled
examples of a target concept `c`. Then `L` is a PAC learning algorithm for `c` using `H` once
`m ≥ c₀((1/ε) log(1/δ) + (d/ε) log(1/ε))`. Stated with the bound of the proof (§3.5.2, p. 61):
for `m ≥ 8/ε`, a random sample fails to be an ε-net for the error regions with probability at
most `2 Φ_d(2m) 2^{−εm/2}`, hence so does a consistent hypothesis fail to have error at most `ε`;
and with the explicit constants `m ≥ (4/ε) log₂(2/δ)` and `m ≥ (8d/ε) log₂(13/ε)` (Blumer,
Ehrenfeucht, Haussler and Warmuth) the failure probability is at most `δ`. Consequently, for
nonempty `H`, every class `C ⊆ H` is PAC learnable using `H` in the sample-complexity sense (for
`H = ∅` no algorithm outputs hypotheses in `H`). `H` is assumed well-behaved
(`IsWellBehaved`), the measurability the double-sample argument needs; without it the statement
is false for some classes of VC dimension `1`. -/
theorem vc_sample_bound {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hHm : ∀ h ∈ H, Measurable h) (d : ℕ) (hd : vcDim H ≤ d) (c : X → Bool) (hc : Measurable c)
    (hwb : IsWellBehaved H c)
    (D : Measure X) [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1) (m : ℕ) (hm : 8 / ε ≤ m) :
    sampleLaw D c m {S | ¬ IsEpsNet H c D ε (samplePoints S)} ≤
      ENNReal.ofReal (2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) ∧
    (∀ L : (Fin m → X × Bool) → X → Bool, (∀ S, L S ∈ H) →
      (∀ S, IsLabeledBy c S → IsConsistent (L S) S) →
      sampleLaw D c m {S | ε < errorOf D c (L S)} ≤
        ENNReal.ofReal (2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2)))) ∧
    (4 / ε * Real.logb 2 (2 / δ) ≤ m → 8 * d / ε * Real.logb 2 (13 / ε) ≤ m →
      ∀ L : (Fin m → X × Bool) → X → Bool, (∀ S, L S ∈ H) →
        (∀ S, IsLabeledBy c S → IsConsistent (L S) S) →
        sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal δ) ∧
    (H.Nonempty → ∀ C : Set (X → Bool), C ⊆ H → (∀ c' ∈ C, IsWellBehaved H c') →
      PACLearnable C H) := by sorry

end ComputationalLearning
