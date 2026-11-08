-- Prove2me | Theorems.Thm_AvoidPlast_corollary_4_3
-- name    : AvoidPlast.corollary_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:49:36.339786+00:00
-- url     : https://prove2.me/theorems/7faf9bd1-c2c5-4094-aef7-e30b7307ab5c
-- title:
--   Corollary 4.3 — PCPP with soundness $2^{-\mathrm{polylog}\,T(m)}$
-- statement:
--   Under the hypotheses of Theorem 4.2, for any $s\ge2^{-\mathrm{polylog}(T(m))}$, $L\in\mathrm{PCPP}_{s,\delta}[r,q,t]$ with $\delta(m)=1/\mathrm{polylog}\,T(m)$, $r(m)=\mathrm{polylog}\,T(m)$, $q(m)=\mathrm{polylog}\,T(m)$ and $t(n,K)=\mathrm{poly}(n,\log K,\log T(m))$. Moreover the verifier is non-adaptive and an accepting proof can be computed deterministically in time $\mathrm{poly}(T(m))$ from $(x,y)$ and a $T(m)$-length witness.
--
--   Differences from the source:
--   - reading: $\mathrm{PCPP}_{s,\delta}[r,q,t]$, not defined in this paper → the [BGH+05] class: a verifier with read-only tapes $x,\rho,y,\pi$; soundness for $y$ that is $\delta$-far; queries counted on $y$ and $\pi$; verification time on the machine; reason: the paper cites the class from [BGH+05] without defining it
--   - reading: proximity parameter $\delta(m)=1/\mathrm{polylog}\,T(m)$ → $\delta(m)=(\log_2T(m)+2)^{-b}$ for every $b$, with the other parameters depending on $b$; reason: the proof of Theorem 4.1 needs $\delta$ below a prescribed $1/\mathrm{polylog}$ (p.20, $\delta_2-\delta_1>1/\mathrm{polylog}$), so the universal reading is the one used and the stronger one
--   - encoding: polylog, poly and $O(\cdot)$ → explicit existential constants $a$, with $\log_2 T(m)+2$ as the base; reason: makes the parameters first-order statements
--   - encoding: $L\in\mathrm{NTIME}[T(m)]$ by a multitape Turing machine, on a pair → a jump-free machine on $(\langle x,y\rangle,w)$, time and witness length $C\cdot T(m)$, $\langle x,y\rangle$ a doubled-bit pairing; reason: footnote 17 fixes the model; the constant is the $O(\cdot)$ of NTIME
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Corollary 4.3, p.18

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

/-- Corollary 4.3 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.18): as Theorem 4.2, for any `s ≥ 2^{-polylog(T(m))}`, with `r(m) =
polylog T(m)`.

**Formalization Note** `δ(m) = (log₂ T(m) + 2)^{-b}` for every `b`, as in `theorem_4_2`. -/
theorem corollary_4_3 (L : List Bool → List Bool → Prop) (T : ℕ → ℕ) (hT : Monotone T)
    (hT0 : ∀ m, 0 < T m) (V₀ : Machine 2) (C : ℕ) (hV₀ : IsPairNTimeVerifier V₀ L T C)
    (s : ℕ → ℝ) (e : ℕ)
    (hs : ∀ m, (2 : ℝ) ^ (-((e : ℝ) * (Real.logb 2 (T m) + 2) ^ e)) ≤ s m) (b : ℕ) :
    ∃ (a : ℕ) (V : Machine 4) (r q : ℕ → ℕ) (t : ℕ → ℕ → ℕ) (P : Machine 3),
      IsPCPP V L (fun x K => s (x.length + K))
        (fun x K => 1 / (Real.logb 2 (T (x.length + K)) + 2) ^ b)
        (fun x K => r (x.length + K)) (fun x K => q (x.length + K)) (fun x K => t x.length K) ∧
      (∀ m, (r m : ℝ) ≤ a * (Real.logb 2 (T m) + 2) ^ a) ∧
      (∀ m, (q m : ℝ) ≤ a * (Real.logb 2 (T m) + 2) ^ a) ∧
      (∀ n K, (t n K : ℝ) ≤ a * ((n : ℝ) + lg K + Real.logb 2 (T (n + K)) + 2) ^ a) ∧
      ∀ x y w : List Bool, w.length ≤ C * T (x.length + y.length) →
        HaltsWithin P ![x, y, w] (a * T (x.length + y.length) ^ a) ∧
        (Accepts V₀ ![UniqueOptScores.pair x y, w] → ∀ ρ : List Bool, ρ.length = r (x.length + y.length) →
          Accepts V ![x, ρ, y, output P ![x, y, w]]) := by sorry

end AvoidPlast
