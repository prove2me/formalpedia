-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_5_8
-- name    : AvoidPlast.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:47:24.885693+00:00
-- url     : https://prove2.me/theorems/a754a92b-558f-4612-aad2-6d73203c6794
-- title:
--   Theorem 5.8 (= Theorem 1.2, general $p$) — low-space simulation of P on average
-- statement:
--   Suppose Assumption 1.1 holds with $p:\mathbb N\to(0,1)$ and $\mathrm{prBP}^*\mathrm L=\mathrm{prL}$. Then for every $L\in\mathsf P$, every $\varepsilon>0$ and every $e\ge1$ there is a deterministic algorithm $A$ of space $n^\varepsilon$ such that
--   $$\Pr_{x\in\{0,1\}^n}[A(x)=L(x)]\ge1-3\bigl(p(N(n))+2^{-(\lg n)^e}\bigr)\quad\text{for all }n\in\mathbb N,$$
--   where $n\le N(n)\le bn^b+b$.
--
--   The base mission states the case $p(n)=n^{-\omega(1)}$ inside Theorem 5.14; here $p$ is general.
--
--   Differences from the source:
--   - reading: Assumption 1.1 holds (with $p$) → Assumption 1.1 with one $p:\mathbb N\to(0,1)$ for every $\varepsilon$; reason: the conclusion is stated in terms of $p$; $p$ has the type $\mathbb N\to(0,1)$ of Assumption 1.1
--   - reading: $p(n^{O(1)})$ → $p(N(n))$ for some $N$ with $n\le N(n)\le bn^b+b$; reason: $p$ is evaluated at the padded input length of the proof, $N=O(n+T^{1/\varepsilon})$; $p$ is not assumed monotone
--   - reading: error $2^{-\mathrm{polylog}(n)}$ → for every $e\ge1$ there is an algorithm with error at most $2^{-(\lg n)^e}$; reason: the proofs choose the polylog freely ($k=\mathrm{polylog}(n)$ repetitions, p.22); "some polylog" would allow $2^{-1}$
--   - encoding: space $n^\varepsilon$ → $O(\cdot)$ with an explicit existential constant, $C\cdot(s(n)+1)$; reason: the mission's reading R2; the $+1$ covers $n=0$
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.8, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_PrBPstarLEqPrL
import Definitions.Def_AvoidPlast_SpaceO
import Definitions.Def_AvoidPlast_lg
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_InP
import Definitions.Def_AvoidPlast_Supplement_Assumption11With

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 5.8 (= Theorem 1.2, one direction, general `p`) (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.25). Suppose Assumption 1.1
holds with `p : ℕ → (0,1)` and `prBP*L = prL`. Then for every `L ∈ P`, every `ε > 0` and every
polylog exponent `e ≥ 1` there is a deterministic machine `A` of space `O(n^ε)` with
`Pr_{x∈{0,1}^n}[A(x) = L(x)] ≥ 1 - 3(p(N(n)) + 2^{-(lg n)^e})` for all `n`, where
`n ≤ N(n) ≤ b n^b + b` (the `p(n^{O(1)})` of the source). -/
theorem theorem_5_8 (p : ℕ → ℝ) (hp : ∀ n, 0 < p n ∧ p n < 1) (hA : Assumption11With p)
    (hD : PrBPstarLEqPrL) :
    ∀ L : Set (List Bool), InP L → ∀ ε : ℝ, 0 < ε → ∀ e : ℝ, 1 ≤ e →
    ∃ (A : Machine 1) (N : ℕ → ℕ) (b : ℕ), SpaceO A (fun n => (n : ℝ) ^ ε) ∧
      (∀ n : ℕ, n ≤ N n ∧ N n ≤ b * n ^ b + b) ∧
      ∀ n : ℕ, 1 - 3 * (p (N n) + (2 : ℝ) ^ (-(lg n) ^ e)) ≤
        prob n (fun x => Accepts A ![x] ↔ x ∈ L) := by sorry

end AvoidPlast.Supplement
