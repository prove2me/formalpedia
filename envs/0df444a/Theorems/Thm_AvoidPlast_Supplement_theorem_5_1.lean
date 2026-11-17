-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_5_1
-- name    : AvoidPlast.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:44:53.125348+00:00
-- url     : https://prove2.me/theorems/e0f61505-0919-47e4-89ec-e23d9ba8aa8c
-- title:
--   Theorem 5.1 — a low-space verifier for sub-linear time from hardness of Avoid
-- statement:
--   There are a universal constant $c>1$ and $\varepsilon_0>0$ such that the following holds. Let $D=\{D_n\}$ be an ensemble of distributions, $p:\mathbb N\to\mathbb R$, $\varepsilon_0>\varepsilon>\delta>0$, $m$ with $n^{c\varepsilon}\le m(n)\le n$, and $C[n^\delta\to m(n)]$ an indexed family. Assume that $\mathrm{Avoid}_C$ cannot be solved by any $\mathrm{SearchNTimeGuess}[\mathrm{poly}(n),n^\varepsilon]$ algorithm with success $p$ or more over $D$. Then for every $L\in\mathrm{NTIME}[n^\varepsilon]$ and every $e\ge1$ there is a probabilistic verifier $V_L$ such that for every $n$:
--
--   1. $V_L$ runs in polynomial time and space $O(n^\delta)$ and makes oracle queries to $C_x$;
--   2. the interaction is one-way, the prover sending $n^\delta$ bits;
--   3. with probability at least $1-p(n)$ over $x\sim D_n$, if $x\in L$ then some prover makes $V_L$ accept with probability $1$;
--   4. every $x\notin L$ is rejected, against every prover, with probability at least $1-2^{-(\lg n)^e}$.
--
--   Moreover, if $\mathrm{Avoid}_C$ cannot be solved by any deterministic polynomial-time algorithm with success $p$ or more over $D$, the same holds for every $L\in\mathrm{DTIME}[n^\varepsilon]$.
--
--   This is the main technical step from hardness of Avoid to space-efficient verification.
--
--   Differences from the source:
--   - reading: "there is a universal constant $c>1$ ... For any pair of sufficiently small constants $\varepsilon>\delta>0$" → $\exists c>1\ \exists\varepsilon_0>0$ before $D$, $p$, $\varepsilon$, $\delta$; reason: the threshold depends only on the PCP of Theorem 4.1 (proof, p.21)
--   - reading: "$\mathrm{Avoid}_C$ cannot be solved ... with success $p$ or more" → for every algorithm of the class and every sufficiently large $n$, the success probability is below $p(n)$; reason: the proof uses the hardness at every large length (Fact 5.1.1, p.21)
--   - reading: error $2^{-\mathrm{polylog}(n)}$ → for every $e\ge1$ there is an algorithm with error at most $2^{-(\lg n)^e}$; reason: the proofs choose the polylog freely ($k=\mathrm{polylog}(n)$ repetitions, p.22); "some polylog" would allow $2^{-1}$
--   - encoding: oracle queries to $C_x$, answers scanned read-once (footnotes 21, 22) → a read-only random-access tape holding $C_x$ at addresses $\langle a,i\rangle$ (`oracleTable`), addresses written on work space; reason: the two models simulate each other with polynomial time overhead and $O(\log n)$ extra space
--   - reading: a probabilistic verifier using space $O(n^\delta)$ → its random string has the fixed length $K(\lceil n^\delta\rceil+1)$ on a read-only tape; reason: within the space bound, so two-way access adds nothing to storing it; a fixed length carries no advice; the proof uses $\mathrm{polylog}(n)$ random bits (p.22)
--   - encoding: the family $C[n^\delta\to m(n),s(n)]$ with $s(\cdot)$ arbitrary → a map $C$ with $|C_x(y)|=m(|x|)$ for $|y|=\lceil|x|^\delta\rceil$; reason: the mission's reading R8
--   - encoding: "the prover sending $n^\delta$ bits"; "with probability $1-p$" → a message of exactly $\lceil n^\delta\rceil$ bits; probability at least $1-p(n)$; reason: reading R3; the usual sense of "with probability"
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.1, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_AvoidPlast_IsNTimeVerifier
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_Supplement_InDTIME
import Definitions.Def_AvoidPlast_Supplement_Ensemble
import Definitions.Def_AvoidPlast_Supplement_AvoidHardSNTG
import Definitions.Def_AvoidPlast_Supplement_AvoidHardDet
import Definitions.Def_AvoidPlast_Supplement_OracleVerifier51

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 5.1, a low-space verifier for sub-linear time from hardness of Avoid (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.21).
There are a universal `c > 1` and `ε₀ > 0` such that for every ensemble `D`, every `p`, all
`ε₀ > ε > δ > 0`, every `m` with `n^{cε} ≤ m(n) ≤ n` and every indexed family `C[n^δ → m(n)]`:
if `Avoid_C` cannot be solved by any `SearchNTimeGuess[poly(n), n^ε]` algorithm with success `p`
or more over `D`, then every `L ∈ NTIME[n^ε]` has, for every polylog exponent `e ≥ 1`, a verifier
with items 1–4 of `OracleVerifier51` for every `n` (polynomial time, space `O(n^δ)`, oracle
`C_x`, one prover message of `n^δ` bits, perfect completeness on a `1 - p` fraction of `D_n`,
soundness error `2^{-(lg n)^e}`). Moreover, under hardness for deterministic polynomial time the
same holds for every `L ∈ DTIME[n^ε]`.

**Formalization Note** `2^{-polylog(n)}` is "for every `e ≥ 1`, error `2^{-(lg n)^e}`" (the proof
takes `k = polylog(n)` repetitions). `s(·)` is arbitrary, so the family is a map (reading R8);
lengths `n^δ`, `n^ε` are `⌈n^δ⌉`, `⌈n^ε⌉` (reading R3). -/
theorem theorem_5_1 : ∃ c : ℝ, 1 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (D : Ensemble) (p : ℕ → ℝ) (ε δ : ℝ), 0 < δ → δ < ε → ε < ε₀ →
    ∀ m : ℕ → ℕ, (∀ n : ℕ, (n : ℝ) ^ (c * ε) ≤ m n ∧ m n ≤ n) →
    ∀ C : List Bool → List Bool → List Bool,
      (∀ x y : List Bool, y.length = ceilPow δ x.length → (C x y).length = m x.length) →
    (AvoidHardSNTG D.dist C (ceilPow δ) m (ceilPow ε) p →
      ∀ (L : Set (List Bool)) (V₀ : Machine 2) (C₀ : ℕ), IsNTimeVerifier V₀ L (ceilPow ε) C₀ →
        ∀ e : ℝ, 1 ≤ e → OracleVerifier51 C m δ D p L e) ∧
    (AvoidHardDet D.dist C (ceilPow δ) m p →
      ∀ L : Set (List Bool), InDTIME (ceilPow ε) L → ∀ e : ℝ, 1 ≤ e →
        OracleVerifier51 C m δ D p L e) := by sorry

end AvoidPlast.Supplement
