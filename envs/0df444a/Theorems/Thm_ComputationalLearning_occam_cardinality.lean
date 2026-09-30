-- Prove2me | Theorems.Thm_ComputationalLearning_occam_cardinality
-- name    : ComputationalLearning.occam_cardinality
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:05:10.082336+00:00
-- url     : https://prove2.me/theorems/d5129c1d-12a7-4adb-8879-37f76f0d42be
-- title:
--   Theorem 2.2 (Occam's Razor, cardinality version): a consistent hypothesis from a finite class H has error > ε with probability ≤ |H|(1 − ε)^m
-- statement:
--   **Theorem 2.2 (Occam's Razor, cardinality version).** Let $C$ be a concept class and $H$ a representation class. Let $L$ be an algorithm such that for any $n$ and any $c \in C_n$, given a sample $S$ of $m$ labeled examples of $c$, $L$ outputs an $h \in H_{n,m}$ consistent with $S$. Then there is a constant $b > 0$ such that for any $n$, any distribution $D$ and any target $c \in C_n$, if $L$ is given a random sample of $m$ examples where $\log|H_{n,m}| \le b\epsilon m - \log(1/\delta)$ (equivalently $m \ge (1/b\epsilon)(\log|H_{n,m}| + \log(1/\delta))$), then $L$ is guaranteed to find a hypothesis $h \in H_{n,m}$ that with probability at least $1 - \delta$ obeys $\mathrm{error}(h) \le \epsilon$.
--
--   Formally, for a measurable target $c$, a distribution $D$, a finite class $H$ of measurable hypotheses, $0 < \epsilon \le 1$ and $\delta > 0$: the probability that a random sample of $m$ examples is consistent with some $h \in H$ of error greater than $\epsilon$ is at most $|H|(1 - \epsilon)^m$ (a fixed bad hypothesis is consistent with probability at most $(1-\epsilon)^m$ by independence, then the union bound); hence it is at most $\delta$ when $m \ge (1/\epsilon)(\ln|H| + \ln(1/\delta))$ (the constant $b = 1$ with natural logarithms); and every algorithm outputting a hypothesis in $H$ consistent with its sample has error greater than $\epsilon$ with probability at most $|H|(1-\epsilon)^m$.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §2.1 pp. 35-36, Theorem 2.2 with its proof (bad hypotheses, independence and the union bound)

import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory

namespace ComputationalLearning

/-- **Theorem 2.2 (Occam's Razor, cardinality version)** (p. 35). Let `H` be a finite hypothesis
class. For any target concept `c`, any distribution `D` and `0 < ε ≤ 1`: the probability that a
random sample of `m` examples is consistent with some hypothesis of `H` of error greater than
`ε` is at most `|H|(1 − ε)^m`; consequently, if `m ≥ (1/ε)(ln|H| + ln(1/δ))` it is at most `δ`,
and any algorithm that outputs a hypothesis in `H` consistent with its sample has error greater
than `ε` with probability at most `|H|(1 − ε)^m` (the book's constant `b` is `1` with natural
logarithms, from `(1 − ε)^m ≤ e^{−εm}`). -/
theorem occam_cardinality {X : Type*} [MeasurableSpace X] (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] (H : Finset (X → Bool)) (hH : ∀ h ∈ H, Measurable h)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (m : ℕ) :
    sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ≤
      ENNReal.ofReal (H.card * (1 - ε) ^ m) ∧
    (1 / ε * (Real.log H.card + Real.log (1 / δ)) ≤ m →
      sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ≤ ENNReal.ofReal δ) ∧
    (∀ L : (Fin m → X × Bool) → X → Bool, (∀ S, L S ∈ H) →
      (∀ S, IsLabeledBy c S → IsConsistent (L S) S) →
      sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal (H.card * (1 - ε) ^ m)) := by sorry

end ComputationalLearning
