-- Prove2me | Theorems.Thm_F3SubsetSum_generator_branch
-- name    : F3SubsetSum.generator_branch
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-15T03:22:42.515488+00:00
-- url     : https://prove2.me/theorems/e77f924c-025f-40b4-9544-660021101eae
-- title:
--   Branching between two circuit generators with an integer clock
-- statement:
--   This is a machine-composition lemma used to assemble the circuit generator of Theorem 1.3.
--
--   Let $G_1,G_2$ be deterministic multi-stack Turing machines with Boolean input and output alphabets, and let $K,d\in\mathbb N$. For $n,m\in\mathbb N$ write $\lceil a/b\rceil$ for the natural-number ceiling $(a+b-1)/b$ (so $\lceil a/0\rceil=0$) and define the clock
--   $$T(n,m)=\lceil m/n\rceil^{\,d\,\lceil n^2/m\rceil}.$$
--   Then there are a machine $G$ and a constant $C\in\mathbb N$ such that for all $n,m,t$ and every output word $w\in\{0,1\}^*$:
--
--   1. if $Kn\le m$ and $G_1$, started on $1^n0\,1^m0\,1^{T(n,m)}$, halts with output $w$ within $t$ steps, then $G$, started on $1^n0\,1^m$, halts with output $w$ within $C\,(t+n+m+T(n,m)+1)^C$ steps;
--   2. if $m<Kn$ and $G_2$, started on $1^n0\,1^m$, halts with output $w$ within $t$ steps, then $G$, started on $1^n0\,1^m$, halts with output $w$ within $C\,(t+n+m+1)^C$ steps.
--
--   So $G$ compares $Kn$ with $m$, and in the first case writes the clock $T(n,m)$ in unary and runs $G_1$, in the second case runs $G_2$ directly. In the proof of Theorem 1.3, $G_1$ is the generator of Theorem 3.1 applied to the decoder of Theorem 1.7 (whose running time is at most $T(n,m)$ for $m\ge Kn$), and $G_2$ is the exhaustive-search generator. The second branch pays no cost for the clock, which may be very large when $m<Kn$.
--
--   **Formalization Note** Machines are `Turing.TM2ComputableAux Bool Bool`, run as in `HMBinPacking.OutputsWithin`; $G$ may depend on $G_1,G_2,K,d$.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, proof of Theorem 1.3, pp.22–23 (assembly of the generator; the running-time bound p.22: every polynomial factor in n, m is g^{O_κ(h)})

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_F3SubsetSum_MachineCodes

namespace F3SubsetSum

/-- **Branching between two generators with an integer clock** (machine plumbing for the proof of
Theorem 1.3 of Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, pp.22–23).

Given machines `G₁`, `G₂` and constants `K`, `d`, there are a machine `G` and a constant `C` such
that on input `1ⁿ 0 1ᵐ`:
* if `Kn ≤ m`, `G` computes the clock `T = ⌈m/n⌉^{d⌈n²/m⌉}` and then behaves like `G₁` on
  `1ⁿ 0 1ᵐ 0 1ᵀ`: whenever `G₁` outputs `out` within `t` steps there, `G` outputs `out` within
  `C(t + n + m + T + 1)^C` steps;
* if `m < Kn`, `G` behaves like `G₂` on the same input `1ⁿ 0 1ᵐ`, with time `C(t + n + m + 1)^C`.

**Formalization Note** Machines are `Turing.TM2ComputableAux Bool Bool`, run as in
`HMBinPacking.OutputsWithin`. The ceilings are natural-number ceilings, written
`⌈a/b⌉ = (a + b − 1)/b` (so the clock is defined for all `n`, `m`). `G` may depend on `G₁`, `G₂`,
`K`, `d`; the constant `C` absorbs the cost of computing the clock and of the comparison. -/
theorem generator_branch (G₁ G₂ : Turing.TM2ComputableAux Bool Bool) (K d : ℕ) :
    ∃ (G : Turing.TM2ComputableAux Bool Bool) (C : ℕ), ∀ (n m t : ℕ) (out : List Bool),
      (K * n ≤ m →
        HMBinPacking.OutputsWithin G₁
          (unaryD n ++ unaryD m ++ unary (((m + n - 1) / n) ^ (d * ((n ^ 2 + m - 1) / m)))) out t →
        HMBinPacking.OutputsWithin G (unaryD n ++ unary m) out
          (C * (t + n + m + ((m + n - 1) / n) ^ (d * ((n ^ 2 + m - 1) / m)) + 1) ^ C)) ∧
      (m < K * n →
        HMBinPacking.OutputsWithin G₂ (unaryD n ++ unary m) out t →
        HMBinPacking.OutputsWithin G (unaryD n ++ unary m) out (C * (t + n + m + 1) ^ C)) := by sorry

end F3SubsetSum
