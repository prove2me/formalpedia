-- Prove2me | Theorems.Thm_AlmostLinearModComp_Composition_theorem_1_1
-- name    : AlmostLinearModComp.Composition.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:19.167393+00:00
-- url     : https://prove2.me/theorems/11e61527-27b7-40c5-a580-36c9dbb02938
-- title:
--   Theorem 1.1 — Almost-linear division-free modular composition
-- statement:
--   There are absolute constants $C_0,C_1>0$ and one deterministic size-only circuit generator such that for every $n\ge2$, every commutative ring $R$ with identity, every monic degree-$n$ polynomial $f\in R[X]$, and all $a,g\in R[X]$ of degree below $n$, the generated division-free circuit returns all $n$ coefficients of
--   $$g(a)\operatorname{rem}f$$
--   using at most
--   $$C_0 n\,2^{C_1\sqrt{\log_2 n}}$$
--   ring operations. Input coefficients are the lower $n$ coefficients of $f$, then those of $a$, then those of $g$; the leading monic coefficient is implicit. All preprocessing is inside the same gate list. Gates are only addition, subtraction and multiplication; constants are integers independent of the ring and coefficient inputs.
--
--   One fixed finite-state bit machine generates the complete circuit, including all integer-constant bits, in at most $A(n+1)^k$ elementary tape transitions for absolute integers $A>0,k\ge0$. This makes explicit the uniformity asserted in the last paragraph of the source proof. The statement assumes no fast arithmetic, precomputed matrix, evaluator, stored array or correctness certificate. It is the single full-strength mission goal, not a correctness-only replacement.
--
--   Differences from the source:
--   - generalization: the displayed theorem states deterministic division-free computation with the almost-linear ring-operation bound → the conclusion also explicitly requires polynomial-time generation of the entire integer-constant circuit; reason: the last paragraph of the source proof asserts this stronger uniformity; dropping that conjunct recovers the displayed theorem
--   - encoding: n·2^{O(sqrt(log n))} ring operations and coefficient-vector inputs → absolute positive C₀,C₁ and a valid gate list with cost at most C₀ n 2^{C₁ sqrt(log₂ n)}, returning all n coefficients; reason: absolute constants absorb the logarithm base and all small n≥2; gate count includes every preprocessing operation
--   - encoding: time polynomial in the numerical degree n for circuit generation → unary n input, binary self-delimiting circuit output, and an explicit one-tape transition bound A(n+1)^k; reason: finite tape machines and polynomial overhead preserve polynomial time in n while accounting for all constant bits
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), Theorem 1.1, printed p.1 / PDF p.2; final proof, especially uniformity paragraph, printed p.8 / PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_Uniformity

namespace AlmostLinearModComp.Composition

/-- Zhou--Wang, STOC 2027 submission #450 (October 2026), Theorem 1.1,
printed p.1 / PDF p.2; uniformity is explicit in its proof, printed p.8 / PDF p.9.
The one machine and absolute constants precede every size, ring and input. -/
theorem theorem_1_1 :
    ∃ (C₀ C₁ : ℝ) (M : CircuitMachine) (A k : ℕ),
      0 < C₀ ∧ 0 < C₁ ∧ 0 < A ∧
      ∀ n : ℕ, 2 ≤ n → ∃ c : Circuit,
        GeneratesCircuit M n (A * (n + 1) ^ k) c ∧
        c.valid (3 * n) n ∧
        (c.cost : ℝ) ≤ C₀ * n * Real.rpow 2 (C₁ * Real.sqrt (Real.logb 2 n)) ∧
        ∀ (R : Type) [CommRing R] (f a g : Polynomial R),
          f.Monic → f.degree = (n : WithBot ℕ) →
          a.degree < (n : WithBot ℕ) → g.degree < (n : WithBot ℕ) →
          c.eval ((List.ofFn fun i : Fin n => f.coeff i) ++
                  (List.ofFn fun i : Fin n => a.coeff i) ++
                  (List.ofFn fun i : Fin n => g.coeff i)) =
            List.ofFn (fun i : Fin n => ((g.comp a) %ₘ f).coeff i) := by sorry

end AlmostLinearModComp.Composition
