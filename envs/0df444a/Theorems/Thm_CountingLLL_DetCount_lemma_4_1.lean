-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_4_1
-- name    : CountingLLL.DetCount.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:13.492205+00:00
-- url     : https://prove2.me/theorems/37d12f1b-49f7-4d9d-bf29-be640c73f396
-- title:
--   Lemma 4.1 — efficiency of the marginal estimator
-- statement:
--   There are two fixed programs $\mathsf{Pre}$ and $\mathsf{Est}$ of the bit-cost oracle RAM and an absolute constant $C$ with the following property. Let $\Phi$ satisfy the standing assumption ($q\ge2$, $k\ge2$, $D\ge1$) and Condition 1.1, with $n$ variables and $m$ constraints.
--   1. $\mathsf{Pre}$, run on the explicit input of $\Phi$, halts within bit time
--   $$C\,(n+kmD)\,\big(1+\log_2(n+m+q)\big)^C .$$
--   2. For every family $\mathcal E$ of constraints, every $c_0\in\mathcal E$ and every $L\ge0$, $\mathsf{Est}$ is started from the final memory of $\mathsf{Pre}$, with a membership array of $\mathcal E$ and with $c_0$ and $L$ in registers. It halts with integers $(a,b)$, $b>0$, $a/b=\hat r^{(L)}_{\mathcal E,c_0}$. It uses at most $q^{CkDL}$ evaluation-oracle calls and bit time at most
--   $$C\,q^{CkDL}\big(1+\log_2(n+m+q)\big)^C .$$
--   For $\mathcal E=\mathcal C$ this is Lemma 4.1: after shared preprocessing in $\tilde O(n+kmD)$ time, $\hat r^{(L)}_{\mathcal C,c_0}$ is computed with $q^{O(kDL)}$ oracle calls in $\tilde O(q^{O(kDL)})$ time.
--
--   Together with Lemma 4.3 and the identity (21), this yields Theorem 1.2.
--
--   Differences from the source:
--   - reading: Õ(n + kmD) and Õ(q^{O(kDL)}) time, q^{O(kDL)} oracle calls → C(n + kmD)(1 + ⌊log₂(n+m+q)⌋)^C, C q^{CkDL}(1 + ⌊log₂(n+m+q)⌋)^C and q^{CkDL}, with one absolute constant C chosen before Φ; reason: Õ suppresses polylogarithmic factors in n, m, q (§1.1 usage); O-constants are absolute
--   - reading: an algorithm in the computational model of §2.5, after shared preprocessing → fixed programs Pre (on the explicit input) and Est (from the final memory of Pre, c₀ in register 0 and L in register 1) of the bit-cost oracle RAM; reason: this is the §2.5 model with explicit scopes and incidence lists; the predicates are reachable only by oracle queries
--   - generalization: the estimate for the whole constraint set C → the estimate for every constraint family E, given by a membership array at the negative addresses of the start memory; reason: E = all constraints (the all-ones array) is the source statement; the proof of Theorem 1.2 needs the prefixes C_i, and the proof of Lemma 4.1 already ranges over all subfamilies
--   - encoding: the estimate r̂^{(L)}_{C,c₀} is computed → the program halts with integers (a, b), b > 0, and a/b equals r̂^{(L)}_{E,c₀} with the index-order enumeration; reason: r̂ is rational; the algorithm fixes one enumeration
--   - encoding: finite variables V and finite domains Q_v → V = Fin n and Q_v = Fin (q v), with q v ≥ 2; reason: every finite source variable space is relabelled bijectively; no constraint function or scope is restricted
--   - generalization: a finite set of constraints C → constraints indexed by Fin m, permitting equal scopes and predicates at different indices; reason: enumerating a source constraint set gives an instance with distinct indices; allowing repetitions preserves that full source case
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Lemma 4.1, PDF p. 12 (printed p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Machine

set_option autoImplicit false

namespace CountingLLL.DetCount

open CSP

/-- Lemma 4.1 (Efficiency of the marginal estimator), with one absolute constant `C` and two
fixed programs `Pre` (shared preprocessing) and `Est` (marginal estimation): for every formula
`Φ` satisfying the standing assumptions and Condition 1.1, `Pre` on the explicit input halts within
`C (n + kmD)(1 + log₂(n+m+q))^C` bit time, and for every constraint family `E` (given by a
membership array), every `c₀ ∈ E` and every `L ≥ 0`, `Est` started from the preprocessed memory
with `c₀, L` in registers halts with the exact rational `r̂^{(L)}_{E,c₀}`, using at most
`q^{CkDL}` oracle calls and `C q^{CkDL} (1 + log₂(n+m+q))^C` bit time. -/
theorem lemma_4_1 :
    ∃ Pre Est : Program, ∃ C : ℕ, 0 < C ∧
      ∀ Φ : CSP, Φ.Standing → Φ.Condition11 →
        ∃ t₀ : ℕ,
          (run Φ Pre (initState (preprocessInput Φ) (fun _ => 0)) t₀).out.isSome ∧
          (run Φ Pre (initState (preprocessInput Φ) (fun _ => 0)) t₀).time ≤
            C * (Φ.n + Φ.kmax * Φ.m * Φ.Dmax) * (1 + Nat.log 2 (Φ.n + Φ.m + Φ.qmax)) ^ C ∧
          ∀ (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m), c₀ ∈ E → ∀ L : ℕ,
            ∃ t : ℕ, ∃ a b : ℤ,
              let s := run Φ Est
                (initState
                  (estimatorMem Φ (run Φ Pre (initState (preprocessInput Φ) (fun _ => 0)) t₀).mem E)
                  (estimatorRegs c₀.val L)) t
              s.out = some (a, b) ∧ 0 < b ∧ (a : ℝ) / (b : ℝ) = Φ.rhat L E c₀ ∧
              s.oracle ≤ Φ.qmax ^ (C * Φ.kmax * Φ.Dmax * L) ∧
              s.time ≤ C * Φ.qmax ^ (C * Φ.kmax * Φ.Dmax * L) *
                (1 + Nat.log 2 (Φ.n + Φ.m + Φ.qmax)) ^ C := by sorry

end CountingLLL.DetCount
