-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_5_9
-- name    : AvoidPlast.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:48:18.586205+00:00
-- url     : https://prove2.me/theorems/df2c0df2-e257-4649-a923-9ded2121cb07
-- title:
--   Theorem 5.9 (= Theorem 1.3) — linear-time $\Sigma_k$ simulation of P on average
-- statement:
--   Suppose Assumption 1.1 holds with $p:\mathbb N\to(0,1)$ for families evaluable in simultaneous time $\mathrm{poly}(n)$ and space $n^{\varepsilon^2}$, and $\mathrm{DSPACE}[O(n)]\not\subseteq\mathrm{i.o.SIZE}^{\mathrm{SAT}}[2^{\delta n}]$ for some $\delta>0$. Then every $L\in\mathsf P$ has a constant $k=k_L$ such that for every $e\ge1$ some linear-time $\Sigma_k$ machine decides $L$ correctly on at least a
--   $$1-3\bigl(p(N(n))+2^{-(\lg n)^e}\bigr)$$
--   fraction of the $n$-bit inputs, for every $n$, where $n\le N(n)\le bn^b+b$.
--
--   Time is traded for alternations: polynomial time becomes linear time with a constant number of alternations, on average.
--
--   Differences from the source:
--   - reading: Assumption 1.1 holds (with $p$) → Assumption 1.1 with one $p:\mathbb N\to(0,1)$ for every $\varepsilon$; reason: the conclusion is stated in terms of $p$; $p$ has the type $\mathbb N\to(0,1)$ of Assumption 1.1
--   - reading: $p(n^{O(1)})$ → $p(N(n))$ for some $N$ with $n\le N(n)\le bn^b+b$; reason: $p$ is evaluated at the padded input length of the proof, $N=O(n+T^{1/\varepsilon})$; $p$ is not assumed monotone
--   - reading: error $2^{-\mathrm{polylog}(n)}$ → for every $e\ge1$ there is an algorithm with error at most $2^{-(\lg n)^e}$; reason: the proofs choose the polylog freely ($k=\mathrm{polylog}(n)$ repetitions, p.22); "some polylog" would allow $2^{-1}$
--   - reading: "decides $L$ correctly on at least ... of the $n$-bit inputs" → for every $n$; reason: the source gives no quantifier; a linear-time $\Sigma_k$ machine can be corrected on finitely many lengths, so this is the stronger form
--   - reading: $k=k_L$ → $k$ is chosen before $e$; reason: "$k=k_L$" depends on $L$ only; the polylog factor in the verifier's time does not change $k$
--   - encoding: SAT-oracle circuits → AND/OR/NOT gates and SAT gates of any fan-in under a fixed CNF encoding; size is the number of gates; reason: the paper fixes no encoding; any two polynomial-time encodings change sizes polynomially, absorbed by $\delta$
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.9, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_lg
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_InP
import Definitions.Def_AvoidPlast_Supplement_IsSigmaMachine
import Definitions.Def_AvoidPlast_Supplement_sigmaAccepts
import Definitions.Def_AvoidPlast_Supplement_SATLowerBound
import Definitions.Def_AvoidPlast_Supplement_Assumption11TSWith

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 5.9 (= Theorem 1.3) (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.25). Suppose Assumption 1.1 holds with `p : ℕ → (0,1)`
for families evaluable in simultaneous time `poly(n)` and space `n^{ε²}`, and
`DSPACE[O(n)] ⊄ i.o.SIZE^SAT[2^{δn}]` for some `δ > 0`. Then every `L ∈ P` has a constant `k = k_L`
such that, for every polylog exponent `e ≥ 1`, a linear-time `Σ_k` machine decides `L` correctly
on at least a `1 - 3(p(N(n)) + 2^{-(lg n)^e})` fraction of the `n`-bit inputs, for every `n`,
where `n ≤ N(n) ≤ b n^b + b`. -/
theorem theorem_5_9 (p : ℕ → ℝ) (hp : ∀ n, 0 < p n ∧ p n < 1) (hA : Assumption11TSWith p)
    (hS : SATLowerBound) :
    ∀ L : Set (List Bool), InP L → ∃ k : ℕ, ∀ e : ℝ, 1 ≤ e →
    ∃ (V : Machine (k + 1)) (C : ℕ) (N : ℕ → ℕ) (b : ℕ), IsSigmaMachine k V (fun n => n) C ∧
      (∀ n : ℕ, n ≤ N n ∧ N n ≤ b * n ^ b + b) ∧
      ∀ n : ℕ, 1 - 3 * (p (N n) + (2 : ℝ) ^ (-(lg n) ^ e)) ≤
        prob n (fun x => sigmaAccepts k V (fun n => n) C x ↔ x ∈ L) := by sorry

end AvoidPlast.Supplement
