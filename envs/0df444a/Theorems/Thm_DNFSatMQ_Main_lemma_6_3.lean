-- Prove2me | Theorems.Thm_DNFSatMQ_Main_lemma_6_3
-- name    : DNFSatMQ.Main.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:32:22.976243+00:00
-- url     : https://prove2.me/theorems/173e9175-422e-4d89-ae8b-518c1c3fd44e
-- title:
--   Lemma 6.3 — covering bound E[µ(Ω \ G_N)] ≤ 1 − σ + √(8^w/N) for any randomized width-≤w rule
-- statement:
--   Let $w\ge0$ and $N\ge1$ be integers and $\Omega = \{0,1\}^d$ with $\mu = U_d$. Consider a fixed randomized procedure that takes $X\sim U_d$ as input and returns a conjunction of width at most $w$ satisfied by $X$, or nothing. Let $\sigma$ be its probability of returning a conjunction, and $G_N$ the union of the conjunctions returned by $N$ independent runs on fresh inputs from $U_d$. Then
--   $$\mathbb E[\mu(\Omega\setminus G_N)] \le 1-\sigma+\sqrt{\frac{8^w}{N}}.$$
--   The procedure is a kernel $K$ assigning to each input $X$ a law on outputs ($\mathsf{none}$ = nothing) whose support contains only conjunctions satisfied by $X$ of width $\le w$; one run has law $U_d \gg\!= K$ and the $N$ runs are independent.
--
--   Differences from the source:
--   - encoding: a term: literals on distinct variables → a partial assignment `Conj n = Fin n → Option Bool`; reason: §2 defines terms as noncontradictory; same objects
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - generalization: a fixed randomized procedure → any Markov kernel from inputs to output laws (`Pt d → PMF (Option (Conj d))`); reason: every randomized procedure, with any source of randomness, defines such a kernel
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Lemma 6.3, p. 24 (PDF 25)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Basic

namespace DNFSatMQ.Main

/-- Lemma 6.3 (p. 24): a randomized procedure is a kernel `K` from inputs to laws of outputs. -/
theorem lemma_6_3 {d : ℕ} (w N : ℕ) (hN : 1 ≤ N) (K : Pt d → PMF (Option (Conj d)))
    (hK : ∀ (X : Pt d) (c : Conj d), some c ∈ (K X).support → c.Sat X ∧ c.width ≤ w) :
    ∑ o : Fin N → Option (Conj d),
        (iidLaw ((PMF.uniformOfFintype (Pt d)).bind K) N o).toReal * uncoveredFrac o ≤
      1 - prob ((PMF.uniformOfFintype (Pt d)).bind K) {o | o.isSome} +
        Real.sqrt ((8 : ℝ) ^ w / N) := by sorry

end DNFSatMQ.Main
