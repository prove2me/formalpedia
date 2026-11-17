-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_7_11
-- name    : AvoidPlast.Supplement.theorem_7_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:56:24.036817+00:00
-- url     : https://prove2.me/theorems/d6a965d8-e6f3-41ca-b896-59b774f96e35
-- title:
--   Theorem 7.11 — an average-case targeted HSG from one-way functions
-- statement:
--   If sub-exponentially secure one-way functions exist, there are constants $\varepsilon\in(0,1)$, $c>0$ and a non-deterministic polynomial-time algorithm $H$ that on $x\in\{0,1\}^n$ uses at most $n^\varepsilon$ non-deterministic bits and outputs on every accepting path $L(n)=n^{O(\varepsilon)}$ strings of length $m(n)=\Theta(n^{\varepsilon^2})$, such that for every coAM procedure $D:\{0,1\}^n\times\{0,1\}^{m(n)}\to\{0,1\}$ whose deterministic verifier runs in time $2^{n^{\varepsilon^2}}$ and uses $r_D(n)=w_D(n)=n^{\varepsilon^3}$ random and witness bits: for infinitely many $n$, with probability at least $n^{-c}$ over $x\in\{0,1\}^n$, if
--   $$\Pr_{y\in\{0,1\}^{m(n)}}[D(x,y)=1]\ge1-2^{m(n)^\varepsilon-m(n)},$$
--   then $H(x)$ has an accepting path, and every accepting path outputs a string $y$ with $D(x,y)=1$.
--
--   Differences from the source:
--   - reading: "sub-exponentially secure one-way functions" (no definition in the paper) → Definition 6.10 without the permutation: polynomial-time $f$, $\rho\in(0,1)$, every inverter of time $2^{n^\rho}$ inverts $f(u)$ with negligible probability for large $n$; reason: this is the security the proofs of Theorems 6.9 and 7.11 contradict (an inverter of time $2^{n^\gamma}$ for every $\gamma>0$)
--   - reading: $L(n)=n^{O(\varepsilon)}$, $m(n)=\Theta(n^{\varepsilon^2})$ → constants $b,b_1>0,b_2$ before $D$ with $L(n)\le n^{b\varepsilon}$ and $b_1n^{\varepsilon^2}\le m(n)\le b_2n^{\varepsilon^2}$ for every large $n$; reason: asymptotic notation with explicit constants
--   - encoding: time $2^{n^{\varepsilon^2}}$, $n^{\varepsilon^3}$ random and witness bits → time $\lceil2^{n^{\varepsilon^2}}\rceil$; exactly $\lceil n^{\varepsilon^3}\rceil$ random and witness bits; reason: reading R3
--   - encoding: $D(x,y)=1$ → Definition 7.4: $\Pr_\rho[\exists w: D(x,y,\rho,w)=0]\le1/3$; reason: the paper's definition
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 7.11, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime
import Definitions.Def_AvoidPlast_Supplement_blockOf
import Definitions.Def_AvoidPlast_Supplement_expBound
import Definitions.Def_AvoidPlast_Supplement_SubexpOWF
import Definitions.Def_AvoidPlast_Supplement_coAMOne

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 7.11, an average-case targeted HSG from cryptography (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.45). If
sub-exponentially secure one-way functions exist, there are `ε ∈ (0,1)`, `c > 0` and a
non-deterministic polynomial-time `H` that on `x ∈ {0,1}^n` uses at most `n^ε` non-deterministic
bits and outputs on every accepting path `L(n) = n^{O(ε)}` strings of length `m(n) = Θ(n^{ε²})`,
such that for every coAM procedure `D` whose deterministic verifier `D(x, y, ρ, w)` runs in time
`2^{n^{ε²}}` with `r_D = w_D = n^{ε³}` random and witness bits: for infinitely many `n`, with
probability at least `n^{-c}` over `x ∈ {0,1}^n`, if `Pr_y[D(x, y) = 1] ≥ 1 - 2^{m(n)^ε - m(n)}` then
`H(x)` has an accepting path and every accepting path outputs a string `y` with `D(x, y) = 1`.

**Formalization Note** The constants in `n^{O(ε)}` and `Θ(n^{ε²})` are existential before `D`;
both bounds hold for every sufficiently large `n`. `D(x, y) = 1` is Definition 7.4 (`coAMOne`). -/
theorem theorem_7_11 (h : SubexpOWF) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ c : ℝ, 0 < c ∧
    ∃ (H : Machine 2) (a : ℕ) (L m : ℕ → ℕ) (b b₁ b₂ : ℝ), IsPolyNTime H a ∧
      (∀ᶠ n : ℕ in Filter.atTop, (L n : ℝ) ≤ (n : ℝ) ^ (b * ε)) ∧
      0 < b₁ ∧ (∀ᶠ n : ℕ in Filter.atTop,
        b₁ * (n : ℝ) ^ (ε ^ 2) ≤ m n ∧ (m n : ℝ) ≤ b₂ * (n : ℝ) ^ (ε ^ 2)) ∧
      (∀ x w : List Bool, w.length ≤ ceilPow ε x.length → Accepts H ![x, w] →
        (output H ![x, w]).length = L x.length * m x.length) ∧
      ∀ D : Machine 4,
        (∀ x y ρ w : List Bool, y.length = m x.length → ρ.length = ceilPow (ε ^ 3) x.length →
          w.length = ceilPow (ε ^ 3) x.length →
          HaltsWithin D ![x, y, ρ, w] (expBound (ε ^ 2) x.length)) →
        ∃ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-c) ≤ prob n fun x =>
          1 - (2 : ℝ) ^ ((m n : ℝ) ^ ε - m n) ≤
              prob (m n) (fun y => coAMOne D (ceilPow (ε ^ 3)) (ceilPow (ε ^ 3)) x y) →
            (∃ w : List Bool, w.length ≤ ceilPow ε n ∧ Accepts H ![x, w]) ∧
            ∀ w : List Bool, w.length ≤ ceilPow ε n → Accepts H ![x, w] →
              ∃ i < L n, coAMOne D (ceilPow (ε ^ 3)) (ceilPow (ε ^ 3)) x
                (blockOf (output H ![x, w]) (m n) i) := by sorry

end AvoidPlast.Supplement
