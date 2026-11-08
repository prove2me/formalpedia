-- Prove2me | Theorems.Thm_AvoidPlast_theorem_4_2
-- name    : AvoidPlast.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:49:28.011198+00:00
-- url     : https://prove2.me/theorems/83585a0d-d52c-44d1-8fd0-c5ebf428de35
-- title:
--   Theorem 4.2 — the PCPP of Ben-Sasson et al. [BGH+05, Theorem 2.5]
-- statement:
--   Let $L$ be a pair language, $n$ the length of the explicit input, $K$ the length of the implicit input and $m=n+K$. If $L\in\mathrm{NTIME}[T(m)]$ for a non-decreasing $T:\mathbb Z^+\to\mathbb Z^+$, then for every constant $s>0$, $L\in\mathrm{PCPP}_{s,\delta}[r,q,t]$ with
--
--   1. proximity parameter $\delta(m)=1/\mathrm{polylog}\,T(m)$,
--   2. randomness complexity $r(m)=\log T(m)+O(\log\log T(m))$,
--   3. query complexity $q(m)=\mathrm{polylog}\,T(m)$,
--   4. verification time $t(n,K)=\mathrm{poly}(n,\log K,\log T(m))$.
--
--   Moreover the verifier makes only non-adaptive queries, and for $(x,y)\in L$ an accepting proof can be deterministically computed in time $\mathrm{poly}(T(m))$ from $(x,y)$ and a $T(m)$-length witness. This is a cited tool: the proof of Theorem 4.1 runs through it.
--
--   Differences from the source:
--   - reading: $\mathrm{PCPP}_{s,\delta}[r,q,t]$, not defined in this paper → the [BGH+05] class: a verifier with read-only tapes $x,\rho,y,\pi$; soundness for $y$ that is $\delta$-far; queries counted on $y$ and $\pi$; verification time on the machine; reason: the paper cites the class from [BGH+05] without defining it
--   - reading: proximity parameter $\delta(m)=1/\mathrm{polylog}\,T(m)$ → $\delta(m)=(\log_2T(m)+2)^{-b}$ for every $b$, with the other parameters depending on $b$; reason: the proof of Theorem 4.1 needs $\delta$ below a prescribed $1/\mathrm{polylog}$ (p.20, $\delta_2-\delta_1>1/\mathrm{polylog}$), so the universal reading is the one used and the stronger one
--   - encoding: polylog, poly and $O(\cdot)$ → explicit existential constants $a$, with $\log_2 T(m)+2$ as the base; reason: makes the parameters first-order statements
--   - encoding: $L\in\mathrm{NTIME}[T(m)]$ by a multitape Turing machine, on a pair → a jump-free machine on $(\langle x,y\rangle,w)$, time and witness length $C\cdot T(m)$, $\langle x,y\rangle$ a doubled-bit pairing; reason: footnote 17 fixes the model; the constant is the $O(\cdot)$ of NTIME
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.2, p.17

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_lg
import Definitions.Def_UniqueOptScores_pair
import Definitions.Def_AvoidPlast_IsPairNTimeVerifier
import Definitions.Def_AvoidPlast_IsPCPP

namespace AvoidPlast

/-- Theorem 4.2, the PCPP of Ben-Sasson et al. [BGH+05, Theorem 2.5] (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.17): for a pair language
`L ∈ NTIME[T(m)]`, `m = n + K`, with `T` non-decreasing, and every constant `s > 0`, `L ∈ PCPP_{s,δ}[r, q, t]`
with `δ(m) = 1/polylog T(m)`, `r(m) = log T(m) + O(log log T(m))`, `q(m) = polylog T(m)` and
`t(n, K) = poly(n, log K, log T(m))`. Moreover the verifier is non-adaptive, and an accepting proof is
computed in time `poly(T(m))` from `(x, y)` and a witness.

**Formalization Note** `δ(m) = (log₂ T(m) + 2)^{-b}` for every `b`: the proof of Theorem 4.1 needs `δ`
below a prescribed `1/polylog`. Reading: [BGH+05]'s class. -/
theorem theorem_4_2 (L : List Bool → List Bool → Prop) (T : ℕ → ℕ) (hT : Monotone T)
    (hT0 : ∀ m, 0 < T m) (V₀ : Machine 2) (C : ℕ) (hV₀ : IsPairNTimeVerifier V₀ L T C)
    (s : ℝ) (hs : 0 < s) (b : ℕ) :
    ∃ (a : ℕ) (V : Machine 4) (r q : ℕ → ℕ) (t : ℕ → ℕ → ℕ) (P : Machine 3),
      IsPCPP V L (fun _ _ => s)
        (fun x K => 1 / (Real.logb 2 (T (x.length + K)) + 2) ^ b)
        (fun x K => r (x.length + K)) (fun x K => q (x.length + K)) (fun x K => t x.length K) ∧
      (∀ m, (r m : ℝ) ≤ Real.logb 2 (T m) + a * Real.logb 2 (Real.logb 2 (T m) + 2) + a) ∧
      (∀ m, (q m : ℝ) ≤ a * (Real.logb 2 (T m) + 2) ^ a) ∧
      (∀ n K, (t n K : ℝ) ≤ a * ((n : ℝ) + lg K + Real.logb 2 (T (n + K)) + 2) ^ a) ∧
      ∀ x y w : List Bool, w.length ≤ C * T (x.length + y.length) →
        HaltsWithin P ![x, y, w] (a * T (x.length + y.length) ^ a) ∧
        (Accepts V₀ ![UniqueOptScores.pair x y, w] → ∀ ρ : List Bool, ρ.length = r (x.length + y.length) →
          Accepts V ![x, ρ, y, output P ![x, y, w]]) := by sorry

end AvoidPlast
