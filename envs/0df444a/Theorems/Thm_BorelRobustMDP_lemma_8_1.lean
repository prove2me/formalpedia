-- Prove2me | Theorems.Thm_BorelRobustMDP_lemma_8_1
-- name    : BorelRobustMDP.lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:29.963458+00:00
-- url     : https://prove2.me/theorems/78e23245-621a-4cac-893a-a43a2c644e21
-- title:
--   Lemma 8.1 — an $L^p$ bound along a convergent sequence in $D_n$
-- statement:
--   Let $v\in\mathbb B_b$ and $n\in\{0,\dots,N-1\}$. Under Assumptions 2.1 and 3.1 (ii), each sequence of random variables
--
--   $$C_k=c_n(x_k,a_k,T_n(x_k,a_k,Z_{n+1}))+v(T_n(x_k,a_k,Z_{n+1}))$$
--
--   induced by a convergent sequence $(x_k,a_k)$ in $D_n$ has an $L^p$-bound $\bar C$: $|C_k|\le\bar C\in L^p(P_{n+1})$ for all $k$.
--
--   This is the envelope for Fatou's lemma in the proof of Theorem 3.10.
--
--   Differences from the source:
--   - reading: under Assumption 3.1 (ii) → under Assumption 3.1 (ii) and Assumption 2.1; reason: the proof uses that D_n is closed, which comes from Assumption 2.1 (i), standing since p.3
--   - reading: a convergent sequence in D_n → a sequence in D_n convergent in E × A; reason: the proof derives that the limit lies in D_n
--   - encoding: Assumption 3.1 (ii): the closed ball B_ϵ(x̄, ā) → a neighbourhood U of (x̄, ā), for the data B : BoundingData; reason: closed balls of a compatible metric are a neighbourhood base
--   - encoding: E and A are Borel spaces → metrizable second countable spaces with Borel σ-algebra that is standard Borel, in one universe; reason: this is a Borel subset of a Polish space; one universe is forced by the platform's Hist E A n
--   - encoding: T_n and c_n are defined on D_n × Z and D_n × E, with their continuity on those sets → total measurable functions on (E × A) × Z and (E × A) × E, with ContinuousOn and LowerSemicontinuousOn on D_n and D_n × E; reason: D_n is measurable, so every paper model extends by a constant, and only values on D_n enter a statement
--   - encoding: stages n = 0, …, N − 1 and ambiguity sets n = 1, …, N → ℕ-indexed families used at n < N and at 1 ≤ n ≤ N, and Fin N for the rules of a policy; N = 0 is not excluded; reason: the other indices are unused, and N = 0 is a harmless empty case
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, Lemma 8.1, p.24

import Mathlib
import Definitions.Def_BorelRobustMDP_Assumption21
import Definitions.Def_BorelRobustMDP_Assumption31
import Definitions.Def_BorelRobustMDP_Bb

open MeasureTheory Filter Topology

namespace BorelRobustMDP

universe u v

/-- Lemma 8.1 (Bäuerle & Glauner, arXiv:2007.13103v1, p.24). For `v ∈ 𝔹_b` and `n < N`, each sequence
`C_k = c_n(x_k, a_k, T_n(x_k, a_k, Z_{n+1})) + v(T_n(x_k, a_k, Z_{n+1}))` induced by a convergent
sequence `(x_k, a_k)` in `D_n` has an `L^p`-bound `C̄`: `|C_k| ≤ C̄ ∈ L^p(P_{n+1})` for all `k`.

**Formalization Note.** The proof's "Since `D_n` is closed" comes from Assumption 2.1 (i), which is the
paper's standing assumption and is a hypothesis here, beside Assumption 3.1 (ii). The sequence
converges in `E × A`, and its limit lies in `D_n` as a consequence. -/
theorem lemma_8_1 {E A : Type u} {Z : Type v} [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A] [MeasurableSpace Z] {N : ℕ}
    (R : RobustModel E A Z N) (B : BoundingData E) (h21 : Assumption21 R.toDecisionModel)
    (h31 : Assumption31_ii R B) (v : E → ℝ) (hv : v ∈ Bb B.b) (n : ℕ) (hn : n < N)
    (y : ℕ → E × A) (ylim : E × A) (hy : ∀ k, y k ∈ R.D n) (hlim : Tendsto y atTop (𝓝 ylim)) :
    ∃ C : Z → ℝ, Measurable C ∧ MemLp C R.p (R.P (n + 1)) ∧
      ∀ k z, |R.c n (y k) (R.T n (y k) z) + v (R.T n (y k) z)| ≤ C z := by sorry

end BorelRobustMDP
