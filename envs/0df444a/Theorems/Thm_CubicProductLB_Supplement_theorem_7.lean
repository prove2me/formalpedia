-- Prove2me | Theorems.Thm_CubicProductLB_Supplement_theorem_7
-- name    : CubicProductLB.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:40:56.73391+00:00
-- url     : https://prove2.me/theorems/a9eea2b4-0db5-4d87-96e4-b8b9d3ea3587
-- title:
--   Theorem 7 — $\mathrm{MOD}_2\circ\mathrm{MOD}_3\circ\mathrm{MOD}_2[2]$ circuits for $[q\mid|x|]$: $\sum_j(t_j+1)^2$, wires and gates
-- statement:
--   Fix an odd prime $q>3$. Let $C$ be a $\mathrm{MOD}_2\circ\mathrm{MOD}_3\circ\mathrm{MOD}_2[2]$ circuit on $n$ Boolean inputs computing the predicate $[q \mid |x|]$ (output $1$ exactly when $q$ divides the number of ones of $x$) at every input. Every bottom $\mathrm{MOD}_2$ gate has fan-in at most two; let $t_j$ be the fan-in of the $j$-th middle $\mathrm{MOD}_3$ gate, after the middle gates computing constant functions are removed. Then:
--
--   1. $$\sum_j (t_j+1)^2 = \Omega_q\!\left(\frac{n^4}{(\log(2+n))^3}\right);$$
--   2. the number $W$ of bottom-to-middle wires satisfies $$W = \Omega_q\!\left(\frac{n^2}{(\log(2+n))^{3/2}}\right);$$
--   3. the total number $S$ of gates, bottom, middle and top, satisfies $$S = \Omega_q\!\left(\frac{n^{4/3}}{\log(2+n)}\right).$$
--
--   Each $\Omega_q$ means: there are $c>0$ and $n_0$, depending only on $q$, such that the quantity is at least $c$ times the displayed bound for every $n \ge n_0$ and every such circuit.
--
--   This is the circuit consequence of the degree-four product lower bound: each middle gate becomes a quartic factor over $\mathbb F_3$ whose occurrence cost is at most a constant times $(t_j+1)^2$.
--
--   **Formalization Note** Circuits are the definition `Mod232Circuit` with $k=2$. "Constant middle gates removed" is read semantically (gates whose output depends on $x$). $W$ counts all bottom-to-middle wires and $S = B+M+1$, as on p.68. $\log$ is the natural logarithm; the exponents $3/2$ and $4/3$ are real powers.
--
--   Differences from the source:
--   - generalization: MOD₃ and MOD₂ gates under one unspecified fixed convention ("a constant c ∈ F₃ depending only on the gate convention", (425)) → every middle gate has its own arbitrary accepting set A ⊆ ℤ/3 and every MOD₂ gate a negation bit; reason: each fixed convention is one choice of the accepting sets and negations, so the Lean statement specializes to it; the proof covers all choices since any function of the residue is a polynomial of degree ≤ 2 in L_G
--   - reading: tⱼ is the fan-in "after constant middle gates are removed" → the sum runs over the middle gates whose output is not constant as a function of x; reason: a constant gate is one computing a constant function; deleting it only flips the top sign
--   - encoding: a layered circuit with the simple-circuit convention (at most one wire between two gates, p.68) → gate inputs are Finsets, and every middle gate feeds the top gate; reason: a middle gate feeding nothing can be deleted without increasing any measure; same instances otherwise
--   - encoding: Ω_q(·) → ∃ c > 0, ∃ n₀, ∀ n ≥ n₀, ∀ circuits computing [q ∣ |x|], quantity ≥ c · bound, one pair of constants per clause; reason: the standard meaning, as in the published goal
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 7, Eqs. (5)–(7), p.5; Section 16, Lemma 51 and Eqs. (429)–(432), pp.67–69

import Mathlib
import Definitions.Def_CubicProductLB_Supplement_Mod232Circuit

namespace CubicProductLB.Supplement

/-- Theorem 7 (Circuit consequence of the degree-four bound) (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 7, Eqs. (5)–(7), p.5; circuit
model of Section 16, pp.67–68). Fix an odd prime `q > 3`. Let `C` be a `MOD2 ∘ MOD3 ∘ MOD2[2]` circuit
on `n` inputs computing `[q ∣ |x|]`, every bottom MOD2 gate of fan-in at most two, and let `t_j` be the
fan-in of the `j`-th middle MOD3 gate after constant middle gates are removed. Then
`Σ_j (t_j + 1)² = Ω_q(n⁴ / (log(2 + n))³)`; the number `W` of bottom-to-middle wires is
`Ω_q(n² / (log(2 + n))^{3/2})`; and the number `S` of gates is `Ω_q(n^{4/3} / log(2 + n))`.

**Formalization Note** Each `Ω_q` is read as: there are `c > 0` and `n₀`, depending only on `q` and
chosen before `n` and the circuit, with the quantity at least `c` times the bound for every `n ≥ n₀`;
each clause has its own constants. "Constant middle gates are removed" is read semantically: the sum
runs over middle gates whose output depends on `x`. `W` counts all bottom-to-middle wires and
`S = B + M + 1` (p.68). `log` is the natural logarithm; the powers `3/2`, `4/3` are real powers. An
odd prime `q > 3` is a prime `q > 3`. -/
theorem theorem_7 (q : ℕ) (hq : q.Prime) (h3 : 3 < q) :
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : Mod232Circuit 2 n, C.Computes q →
      c * (n : ℝ) ^ 4 / Real.log (2 + n) ^ 3 ≤ (C.quadCost : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : Mod232Circuit 2 n, C.Computes q →
      c * (n : ℝ) ^ 2 / Real.log (2 + n) ^ ((3 : ℝ) / 2) ≤ (C.wires : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : Mod232Circuit 2 n, C.Computes q →
      c * (n : ℝ) ^ ((4 : ℝ) / 3) / Real.log (2 + n) ≤ (C.size : ℝ)) := by sorry

end CubicProductLB.Supplement
