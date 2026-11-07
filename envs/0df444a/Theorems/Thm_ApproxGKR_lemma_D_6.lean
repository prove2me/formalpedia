-- Prove2me | Theorems.Thm_ApproxGKR_lemma_D_6
-- name    : ApproxGKR.lemma_D_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:48.141008+00:00
-- url     : https://prove2.me/theorems/4a98aee4-d262-490d-9d47-83da7371c922
-- title:
--   Lemma D.6 — root approximation with each output bit in logarithmic space
-- statement:
--   There are a map $(p,N,j)\mapsto\mathrm{Root}_p(j,N)=(A+iB)2^{-p}$ with $A,B\in\mathbb Z$, one RAM program and a constant $c$ such that for all integers $p\ge1$, $N\ge2$ and $0\le j<N$:
--   1. $\big|\mathrm{Root}_p(j,N)-\exp(2\pi ij/N)\big|<2^{1-p}$;
--   2. on input $(p,N,j,\mathrm{comp},\iota)$ with $\mathrm{comp}\in\{0,1\}$ and $\iota<p+3$, the program outputs bit $\iota$ of the width-$(p+3)$ two's-complement encoding of $A$ (comp $=0$) or $B$ (comp $=1$), in time at most $c(p+\log_2N+2)^c$ and space at most $c\log_2(p+\log_2N+2)$, whatever the oracle answers.
--
--   The verifier and the honest prover approximate the roots of unity they need with this algorithm.
--
--   Differences from the source:
--   - reading: "there is a fixed algorithm"; "each output bit is computable in space O(log(p + log N + 2)) and time poly(p + log N)" → one program of the mission's online log-cost RAM that, on the encoded query (p, N, j, comp, ι), outputs that bit within time c(p + log₂N + 2)^c and space c·log₂(p + log₂N + 2); reason: the paper names no machine; a single program with explicit bounds is the literal content of the claim
--   - encoding: components in 2^{−p}ℤ → integers (A, B) with value (A + iB)2^{−p}; output bits of the width-(p + 3) two's-complement encoding; reason: |A|, |B| ≤ 2^p + 2 fit in p + 3 signed bits
--   - encoding: log N → Nat.log 2 N; reason: base two (p.5), integer part
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), App. D.2.2, Lemma D.6, p.53

import Mathlib
import Definitions.Def_ApproxGKR_root
import Definitions.Def_ApproxGKR_dyadicVal
import Definitions.Def_ApproxGKR_RAMRun
import Definitions.Def_ApproxGKR_Instance

namespace ApproxGKR

/-- **Lemma D.6 (root approximation in logarithmic space)** (p.53).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), App. D.2.2, Lemma D.6, p.53: "For integers `p ≥ 1`, `N ≥ 2`, and `0 ≤ j < N`,
there is a fixed algorithm returning a complex number `Rootp(j, N)` with components in `2^{−p}Z`
such that `|Rootp(j, N) − exp(2πij/N)| < 2^{1−p}`. Each output bit is computable in space
`O(log(p + log N + 2))` and time `poly(p + log N)`."

There are a map `Root_p(j, N) = (A + iB)2^{−p}` and one RAM program such that for all `p ≥ 1`,
`N ≥ 2`, `j < N` the approximation bound holds, and on input `(p, N, j, comp, ι)` the program
outputs bit `ι < p + 3` of the width-`(p + 3)` two's-complement encoding of component `comp`
(`0` real, `1` imaginary) within time `c(p + log N + 2)^c` and space `c·log(p + log N + 2)`.

**Formalization Note** "Each output bit is computable" is read as: a single program, run on the
encoded query `(p, N, j, comp, ι)`, outputs that bit; the machine is the mission's online log-cost
RAM in one phase (`SRun`), with any oracle answers (the program does not need the oracle).
Width `p + 3` suffices because `|A|, |B| ≤ 2^p + 2`. `log` is `Nat.log 2`. -/
theorem lemma_D_6 :
    ∃ (Root : ℕ → ℕ → ℕ → ℤ × ℤ) (P : Program) (c : ℕ),
      ∀ p N j : ℕ, 1 ≤ p → 2 ≤ N → j < N →
        ‖dyadicVal ((Root p N j).1, (Root p N j).2, p) - root N j‖ < (2 : ℝ) ^ (1 - (p : ℤ)) ∧
        ∀ comp ι : ℕ, comp < 2 → ι < p + 3 → ∀ O : OracleAnswers,
          ∃ time space : ℕ,
            SRun P (encNats [p, N, j, comp, ι]) O
              [twosBit (if comp = 0 then (Root p N j).1 else (Root p N j).2) (p + 3) ι]
              time space ∧
            time ≤ c * (p + Nat.log 2 N + 2) ^ c ∧
            space ≤ c * Nat.log 2 (p + Nat.log 2 N + 2) := by sorry

end ApproxGKR
