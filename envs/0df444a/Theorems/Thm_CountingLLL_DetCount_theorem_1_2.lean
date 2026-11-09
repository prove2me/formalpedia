-- Prove2me | Theorems.Thm_CountingLLL_DetCount_theorem_1_2
-- name    : CountingLLL.DetCount.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:12.560217+00:00
-- url     : https://prove2.me/theorems/dd57bb43-923c-43fa-9482-f318f443edba
-- title:
--   Theorem 1.2 — deterministic approximate counting of CSP solutions
-- statement:
--   There are a single deterministic program $\mathsf P$ of the bit-cost oracle RAM and a single absolute constant $C>0$ with the following property. Let $\Phi=(V,\mathcal Q,\mathcal C)$ be any CSP formula satisfying the standing assumption $q\ge2$, $k\ge2$, $D\ge1$ and Condition 1.1,
--   $$4\mathrm e\,p\,(D+1)^2\le1,$$
--   and let $0<\varepsilon<1$ be any real accuracy. Run $\mathsf P$ on the explicit input of $\Phi$ (domain sizes, scopes and incidence lists), with the precision request $s(\varepsilon)=\max(1,\lceil\log_2(1/\varepsilon)\rceil)$ and with access to the constraint functions only through the evaluation oracle of Assumption 1. The run halts with integers $(a,b)$, $b>0$, whose quotient $\hat Z_\Phi=a/b$ satisfies
--   $$(1-\varepsilon)Z_\Phi\le\hat Z_\Phi\le(1+\varepsilon)Z_\Phi.$$
--   Both the number of oracle calls and the bit running time of the run are at most
--   $$\Big(\frac{nD}{\varepsilon}\Big)^{C\,k\,D\,\log q}.$$
--
--   For fixed $k$, $D$ and $q$ this is a fully polynomial-time approximation scheme for the number of solutions in the counting-LLL regime $pD^2\lesssim1$.
--
--   Differences from the source:
--   - reading: a deterministic algorithm with access to the evaluation oracle, in the computational model of §2.5 → one fixed program of the bit-cost oracle RAM defined in the Machine module, fixed before Φ and ε, on the explicit input layout; the predicates are reachable only by the query instruction; reason: §2.5 specifies a random-access model with binary integers, bit costs and unit-cost oracle calls
--   - reading: an accuracy parameter 0 < ε < 1 → every real ε in (0, 1), supplied to the machine as the precision request s(ε) = max(1, ⌈log₂(1/ε)⌉), i.e. the dyadic tolerance η = 2^{−s} with ε/2 < η ≤ ε; reason: §2.5 specifies binary rationals but no representation of a real accuracy; the goal still quantifies over every real ε, and the factor 2 in 1/η is absorbed in the exponent constant
--   - reading: bounded by (nD/ε)^{O(kD log q)} in the worst case → at most (nD/ε)^{C·k·D·ln q} for one absolute C > 0 chosen before Φ and ε, for the unique (deterministic) run; reason: the O-constant is absolute; the base of the logarithm is absorbed into C
--   - encoding: an estimate Ẑ_Φ → the output pair of integers (a, b), b > 0, with Ẑ_Φ = a/b; reason: rationals are pairs of binary integers in §2.5
--   - encoding: finite variables V and finite domains Q_v → V = Fin n and Q_v = Fin (q v), with q v ≥ 2; reason: every finite source variable space is relabelled bijectively; no constraint function or scope is restricted
--   - generalization: a finite set of constraints C → constraints indexed by Fin m, permitting equal scopes and predicates at different indices; reason: enumerating a source constraint set gives an instance with distinct indices; allowing repetitions preserves that full source case
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Theorem 1.2 (proof §4.2, PDF pp. 14–15), PDF p. 3 (printed p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Machine

set_option autoImplicit false

namespace CountingLLL.DetCount

open CSP

/-- Theorem 1.2 (Deterministic approximate counting). There are one fixed program `P` of the
bit-cost oracle RAM and one absolute constant `C > 0` such that for every CSP formula `Φ`
satisfying the standing assumptions (`q ≥ 2`, `k ≥ 2`, `D ≥ 1`) and Condition 1.1, and every real
`0 < ε < 1`, the run of `P` on the explicit input of `Φ` with precision request `s(ε)` (and
oracle access to the constraints only through `query`) halts with integers `(a, b)`, `b > 0`, such
that `(1 − ε) Z_Φ ≤ a/b ≤ (1 + ε) Z_Φ`, and both its number of oracle calls and its bit running
time are at most `(nD/ε)^{C·k·D·log q}`. -/
theorem theorem_1_2 :
    ∃ P : Program, ∃ C : ℝ, 0 < C ∧
      ∀ Φ : CSP, Φ.Standing → Φ.Condition11 →
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          ∃ t : ℕ, ∃ a b : ℤ,
            let s := run Φ P (initState (countingInput Φ (precisionCode ε)) (fun _ => 0)) t
            s.out = some (a, b) ∧ 0 < b ∧
            (1 - ε) * (Φ.ZPhi : ℝ) ≤ (a : ℝ) / (b : ℝ) ∧
            (a : ℝ) / (b : ℝ) ≤ (1 + ε) * (Φ.ZPhi : ℝ) ∧
            (s.oracle : ℝ) ≤
              ((Φ.n : ℝ) * (Φ.Dmax : ℝ) / ε) ^ (C * Φ.kmax * Φ.Dmax * Real.log Φ.qmax) ∧
            (s.time : ℝ) ≤
              ((Φ.n : ℝ) * (Φ.Dmax : ℝ) / ε) ^ (C * Φ.kmax * Φ.Dmax * Real.log Φ.qmax) := by sorry

end CountingLLL.DetCount
