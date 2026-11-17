-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_5_4
-- name    : AvoidPlast.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:46:05.649211+00:00
-- url     : https://prove2.me/theorems/866c542a-34ad-46d9-86e4-d9c74143470b
-- title:
--   Theorem 5.4 — simulating NP by a low-space AM verifier from hardness of Avoid
-- statement:
--   There are a universal $c>1$ and $\varepsilon_0>0$ such that the following holds. Let $\delta>0$, let $X,Y$ be ensembles with $Y$ samplable in polynomial time and space $n^\delta$, and let $T$ be a nice increasing function with $T(n)\ge n$. Let $\delta<\varepsilon<\varepsilon_0$, $m$ with $n^{c\varepsilon}\le m(n)\le n$, and $C[n^\delta\to m(n)]$ an indexed family such that $\mathrm{Avoid}_C$ cannot be solved by any $\mathrm{SearchNTimeGuess}[\mathrm{poly}(n),n^\varepsilon]$ algorithm with success $p(n)$ or more over $XY^{T^{1/\varepsilon}}$. Then for every $L\in\mathrm{NTIME}[T]$ and every $e\ge1$ there is an AM verifier $V_L$ with:
--
--   1. time $T^{O(1/\varepsilon)}$ and space $O(T^{\delta/\varepsilon})$, not counting its randomness, which is stored on a read-only two-way tape; oracle queries to $C_{xy}$ with $y\sim Y_{T(n)^{1/\varepsilon}}$;
--   2. one round (two messages), the honest prover's message having $T^{\delta/\varepsilon}$ bits;
--   3. with probability at least $1-p(N)$ over $x\sim X_n$ and the coins, $N=n+T(n)^{1/\varepsilon}$, if $x\in L$ then some prover message makes $V_L$ accept;
--   4. every $x\notin L$ is rejected, against every prover, with probability at least $1-2^{-(\lg N)^e}$.
--
--   Moreover, under hardness for deterministic polynomial time over $XY^{T^{1/\varepsilon}}$ the same holds for every $L\in\mathrm{DTIME}[T]$.
--
--   Differences from the source:
--   - reading: "Let $c>1$ be the universal constant from Theorem 5.1" → $\exists c>1$ in this statement; reason: a statement cannot name another theorem's witness; the proof uses only $c$'s role in Theorem 5.1
--   - reading: "for a sufficiently small $\varepsilon>\delta$" → $\exists\varepsilon_0>0$ before $\delta$, then $\delta<\varepsilon<\varepsilon_0$; reason: as in Theorem 5.1
--   - reading: "$\mathrm{Avoid}_C$ cannot be solved ... with success $p$ or more" → for every algorithm of the class and every sufficiently large $n$, the success probability is below $p(n)$; reason: the proof uses the hardness at every large length (Fact 5.1.1, p.21)
--   - reading: error $2^{-\mathrm{polylog}(n)}$ → for every $e\ge1$ there is an algorithm with error at most $2^{-(\lg n)^e}$; reason: the proofs choose the polylog freely ($k=\mathrm{polylog}(n)$ repetitions, p.22); "some polylog" would allow $2^{-1}$
--   - encoding: oracle queries to $C_x$, answers scanned read-once (footnotes 21, 22) → a read-only random-access tape holding $C_x$ at addresses $\langle a,i\rangle$ (`oracleTable`), addresses written on work space; reason: the two models simulate each other with polynomial time overhead and $O(\log n)$ extra space
--   - reading: the verifier draws $y\sim Y_{T(n)^{1/\varepsilon}}$ with its own coins → $y$ is given to the verifier as part of its persistent randomness; reason: the sampler of $Y$ runs in time $\mathrm{poly}(T^{1/\varepsilon})$ and space $O(T^{\delta/\varepsilon})$, within the stated bounds, so such a verifier is a verifier of the source's form
--   - encoding: time $T^{O(1/\varepsilon)}$; $T(n)^{1/\varepsilon}$; message of $T^{\delta/\varepsilon}$ bits → $\lceil a(T(n)^{a/\varepsilon}+1)\rceil$ with $a$ after $L$ (also the length of the coins); $\lceil T(n)^{1/\varepsilon}\rceil$; exactly $\lceil T(n)^{\delta/\varepsilon}\rceil$ bits; reason: readings R2, R3; a fixed coin length carries no advice
--   - encoding: Definition 5.3 when no $n$ has $N\ge n+T_0(n)$ → $n=0$; reason: undefined in the source; only $N<T_0(0)$, finitely many lengths, which asymptotic hardness ignores
--   - encoding: "$Y$ samplable in polynomial time and space $n^\delta$" → a sampler with coins of fixed length $a(N^a+1)$, time $a(N^a+1)$, work space $a(N^\delta+1)$, exact output law $Y_N$; reason: Definition 3.4 with the space bound
--   - reading: "$T$ a nice increasing function" → `IsNice T`, `Monotone T` (non-decreasing), $n\le T(n)$; reason: "increasing" is ambiguous; non-decreasing is the weaker hypothesis, so the stronger theorem; the padding step needs only that $n+\lceil T(n)^{1/\varepsilon}\rceil$ increase strictly, which holds for every non-decreasing $T$
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.4, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_AvoidPlast_IsNTimeVerifier
import Definitions.Def_AvoidPlast_IsNice
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_Supplement_InDTIME
import Definitions.Def_AvoidPlast_Supplement_Ensemble
import Definitions.Def_AvoidPlast_Supplement_paddedDist
import Definitions.Def_AvoidPlast_Supplement_IsSampler
import Definitions.Def_AvoidPlast_Supplement_AvoidHardSNTG
import Definitions.Def_AvoidPlast_Supplement_AvoidHardDet
import Definitions.Def_AvoidPlast_Supplement_padExp
import Definitions.Def_AvoidPlast_Supplement_AMVerifier54

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 5.4, simulating NP by a low-space AM verifier from hardness of Avoid (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.23).
There are a universal `c > 1` and `ε₀ > 0` such that the following holds. Let `δ > 0`, let `X`, `Y`
be ensembles with `Y` samplable in polynomial time and space `n^δ`, and let `T` be nice,
increasing (non-decreasing, `Monotone`), with `T(n) ≥ n`. For `δ < ε < ε₀`, `m` with `n^{cε} ≤ m(n) ≤ n` and an indexed family
`C[n^δ → m(n)]`: if `Avoid_C` cannot be solved by any `SearchNTimeGuess[poly(n), n^ε]` algorithm
with success `p(n)` or more over `XY^{T^{1/ε}}`, then every `L ∈ NTIME[T]` has, for every `e ≥ 1`,
an AM verifier with items 1–4 of `AMVerifier54`. Moreover, under hardness for deterministic
polynomial time over `XY^{T^{1/ε}}`, the same holds for every `L ∈ DTIME[T]`.

**Formalization Note** The constant `c` is existential here (the source points to Theorem 5.1's).
`T(n)^{1/ε}` is `⌈T(n)^{1/ε}⌉`; `2^{-polylog(N)}` reads as in Theorem 5.1. "Increasing" is read as
non-decreasing, the weaker hypothesis: `n + ⌈T(n)^{1/ε}⌉` is strictly increasing either way, which
is all the padding step uses. -/
theorem theorem_5_4 : ∃ c : ℝ, 1 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ δ : ℝ, 0 < δ → ∀ X Y : Ensemble, (∃ (S : Machine 2) (aS : ℕ), IsSampler S aS Y δ) →
    ∀ T : ℕ → ℕ, IsNice T → Monotone T → (∀ n, n ≤ T n) →
    ∀ (p : ℕ → ℝ) (ε : ℝ), δ < ε → ε < ε₀ →
    ∀ m : ℕ → ℕ, (∀ n : ℕ, (n : ℝ) ^ (c * ε) ≤ m n ∧ m n ≤ n) →
    ∀ C : List Bool → List Bool → List Bool,
      (∀ x y : List Bool, y.length = ceilPow δ x.length → (C x y).length = m x.length) →
    (AvoidHardSNTG (paddedDist X Y (padExp T ε)) C (ceilPow δ) m (ceilPow ε) p →
      ∀ (L : Set (List Bool)) (V₀ : Machine 2) (C₀ : ℕ), IsNTimeVerifier V₀ L T C₀ →
        ∀ e : ℝ, 1 ≤ e → AMVerifier54 C m δ ε T X Y p L e) ∧
    (AvoidHardDet (paddedDist X Y (padExp T ε)) C (ceilPow δ) m p →
      ∀ L : Set (List Bool), InDTIME T L → ∀ e : ℝ, 1 ≤ e →
        AMVerifier54 C m δ ε T X Y p L e) := by sorry

end AvoidPlast.Supplement
