-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_5_6
-- name    : AvoidPlast.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:46:42.666225+00:00
-- url     : https://prove2.me/theorems/a3ec00f5-0240-4de9-9fce-d9bf34ce175f
-- title:
--   Theorem 5.6 (= Theorem 2.1) — low-space AM verifiers for P
-- statement:
--   Suppose Assumption 1.1 holds with $p:\mathbb N\to(0,1)$ for families evaluable in simultaneous time $\mathrm{poly}(n)$ and space $n^{\varepsilon^2}$. Then for every $L\in\mathsf P$, every $\gamma>0$ and every $e\ge1$ there is an AM verifier $V$ with:
--
--   1. complexity: $V$ runs in time $\mathrm{poly}(n)$, uses space $O(n^\gamma)$, has prover messages of $n^\gamma$ bits and $\mathrm{poly}(n)$ bits of persistent randomness (read-only, two-way);
--   2. average-case completeness: with probability at least $1-p(N(n))-2^{-(\lg n)^e}$ over $x\in\{0,1\}^n$ and the coins, if $x\in L$ then some prover message makes $V$ accept;
--   3. worst-case soundness: for every $x\notin L$, the probability over the coins that some prover message makes $V$ accept is at most $2^{-(\lg n)^e}$,
--
--   where $n\le N(n)\le bn^b+b$.
--
--   This is the "master result" of the paper: Theorems 5.8 and 5.9 derandomize this verifier.
--
--   Differences from the source:
--   - reading: Assumption 1.1 holds (with $p$) → Assumption 1.1 with one $p:\mathbb N\to(0,1)$ for every $\varepsilon$; reason: the conclusion is stated in terms of $p$; $p$ has the type $\mathbb N\to(0,1)$ of Assumption 1.1
--   - reading: $p(n^{O(1)})$ → $p(N(n))$ for some $N$ with $n\le N(n)\le bn^b+b$; reason: $p$ is evaluated at the padded input length of the proof, $N=O(n+T^{1/\varepsilon})$; $p$ is not assumed monotone
--   - reading: error $2^{-\mathrm{polylog}(n)}$ → for every $e\ge1$ there is an algorithm with error at most $2^{-(\lg n)^e}$; reason: the proofs choose the polylog freely ($k=\mathrm{polylog}(n)$ repetitions, p.22); "some polylog" would allow $2^{-1}$
--   - reading: "uses at most $n^\gamma$ space" → space $O(n^\gamma)$; reason: reading R2; a literal $n^\gamma$ fails at $n=0$
--   - encoding: message length $n^\gamma$; $\mathrm{poly}(n)$ persistent random bits → exactly $\lceil n^\gamma\rceil$ bits; coins of the fixed length $a(n^a+1)$; reason: reading R3; a fixed coin length carries no advice
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.6, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_lg
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_workSpace
import Definitions.Def_AvoidPlast_Supplement_InP
import Definitions.Def_AvoidPlast_Supplement_Assumption11TSWith

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 5.6 (= Theorem 2.1) (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.24). Suppose Assumption 1.1 holds with `p` for families
evaluable in simultaneous time `poly(n)` and space `n^{ε²}`. Then for every `L ∈ P`, every `γ > 0`
and every polylog exponent `e ≥ 1` there is an AM verifier `V(x, ρ, z)` that runs in time
`poly(n)` and space `O(n^γ)`, has prover messages of `⌈n^γ⌉` bits and `poly(n)` bits of persistent
randomness `ρ` (a read-only tape, not counted as space), and satisfies

* average-case completeness: with probability at least `1 - p(N(n)) - 2^{-(lg n)^e}` over
  `x ∈ {0,1}^n` and `ρ`, if `x ∈ L` then some message makes `V` accept;
* worst-case soundness: for every `x ∉ L`, `Pr_ρ[∃ z : V(x, ρ, z) accepts] ≤ 2^{-(lg n)^e}`,

where `n ≤ N(n) ≤ b n^b + b` (the `p(n^{O(1)})` of the source).

**Formalization Note** "Uses at most `n^γ` space" is `O(n^γ)` (reading R2). -/
theorem theorem_5_6 (p : ℕ → ℝ) (hp : ∀ n, 0 < p n ∧ p n < 1) (hA : Assumption11TSWith p) :
    ∀ L : Set (List Bool), InP L → ∀ γ : ℝ, 0 < γ → ∀ e : ℝ, 1 ≤ e →
    ∃ (V : Machine 3) (a : ℕ) (K : ℝ) (N : ℕ → ℕ) (b : ℕ),
      (∀ x ρ z : List Bool, ρ.length = a * (x.length ^ a + 1) → z.length = ceilPow γ x.length →
        HaltsWithin V ![x, ρ, z] (a * (x.length ^ a + 1)) ∧
        (workSpace V ![x, ρ, z] : ℝ) ≤ K * ((x.length : ℝ) ^ γ + 1)) ∧
      (∀ n : ℕ, n ≤ N n ∧ N n ≤ b * n ^ b + b) ∧
      (∀ n : ℕ, 1 - p (N n) - (2 : ℝ) ^ (-(lg n) ^ e) ≤
        prob (n + a * (n ^ a + 1)) fun xρ => xρ.take n ∈ L →
          ∃ z : List Bool, z.length = ceilPow γ n ∧ Accepts V ![xρ.take n, xρ.drop n, z]) ∧
      ∀ x : List Bool, x ∉ L →
        prob (a * (x.length ^ a + 1)) (fun ρ =>
          ∃ z : List Bool, z.length = ceilPow γ x.length ∧ Accepts V ![x, ρ, z])
          ≤ (2 : ℝ) ^ (-(lg x.length) ^ e) := by sorry

end AvoidPlast.Supplement
