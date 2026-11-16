-- Prove2me | Theorems.Thm_DDNNFNeg_Supplement_theorem_1_2
-- name    : DDNNFNeg.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:48:54.122205+00:00
-- url     : https://prove2.me/theorems/530c52f0-58ca-48cd-82f2-0981df61172a
-- title:
--   Theorem 1.2 (Quasipolynomial Separation for a Structured Input) — some $f$ has a structured d-DNNF of size $O(n)$ while every DNNF for $\neg f$ has size $n^{\Omega(\log n)}$
-- statement:
--   There are constants $C, c > 0$ such that for infinitely many $n \in \mathbb N$ there is a Boolean function $f : \{0,1\}^n \to \{0,1\}$ with the following two properties.
--
--   1. $f$ is computed by a **structured d-DNNF** (an NNF with literal input gates that is decomposable, deterministic and respects a single vtree over the $n$ variables) with at most $C n$ gates.
--   2. Every DNNF computing $\neg f$ has at least
--   $$n^{c \log n}$$
--   gates.
--
--   The lower bound holds even though the DNNF for $\neg f$ is required to be neither structured nor deterministic. This strengthens Vinall-Smeeth's quasipolynomial separation for structured DNNFs to general DNNFs, and it is the separation used for the automata and grammar applications (Theorem 1.4).
--
--   **Formalization Note** The constants are fixed before "for infinitely many $n$" (for every $N$ there is $n \ge N$); $\log$ is the natural logarithm, and $n^{c\log n}$ is a real power. Sizes count all gates, input gates included.
--
--   Differences from the source:
--   - reading: size O(n), size n^{Ω(log n)}, for infinitely many n → constants C, c > 0 fixed first, then ∀ N ∃ n ≥ N with size ≤ C·n and size ≥ n^{c·ln n}; reason: standard reading of asymptotic notation, the same as in the published goal DDNNFNeg.theorem_1_1
--   - reading: structured d-DNNF (described informally, defined in [AAC+24]) → constant-free d-DNNF respecting one vtree over the variables (Pipatsrisawat–Darwiche definition); reason: the paper defers the definition to the cited literature; this is its standard form
--   - generalization: every DNNF computing ¬f (NNFs have literal input gates) → every DNNF computing ¬f, constant leaves also allowed; reason: a larger class of circuits; it contains the paper's DNNFs, so the bound specializes to the source; it also prevents the trivialization by f ≡ 1, since no constant-free DNNF computes the constant 0
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Theorem 1.2, p.4 (proof §6.2, p.18)

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_Computes
import Definitions.Def_DDNNFNeg_NNF_IsConstFree
import Definitions.Def_DDNNFNeg_NNF_IsDDNNF
import Definitions.Def_DDNNFNeg_Supplement_IsStructured

namespace DDNNFNeg.Supplement

/-- **Theorem 1.2** (Quasipolynomial Separation for a Structured Input) (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.4; proof §6.2,
p.18): for infinitely many `n ∈ ℕ`, there is a Boolean function `f : {0,1}^n → {0,1}` such that
`f` is computable by a structured d-DNNF of size `O(n)` but every DNNF computing `¬f` has size
`n^{Ω(log n)}`.

**Formalization Note** The constants `C, c > 0` of `O(n)` and `n^{Ω(log n)}` are fixed before
"for infinitely many `n`" (`∀ N, ∃ n ≥ N`); `n^{c log n}` is a real power with the natural
logarithm (another base only rescales `c`). The structured d-DNNF is in the paper's class:
constant-free, decomposable, deterministic, and respecting one vtree over the `n` variables.
The lower bound quantifies over every DNNF (not necessarily deterministic or structured), with
constant leaves also allowed, as in the published goal `DDNNFNeg.theorem_1_1`. -/
theorem theorem_1_2 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, ∃ n ≥ N, ∃ f : (Fin n → Bool) → Bool,
      (∃ D : NNF (Fin n), D.IsConstFree ∧ D.IsDDNNF ∧ IsStructured D ∧ D.Computes f ∧
        (D.size : ℝ) ≤ C * n) ∧
      (∀ D : NNF (Fin n), D.IsDNNF → D.Computes (fun x => !f x) →
        (n : ℝ) ^ (c * Real.log n) ≤ (D.size : ℝ)) := by sorry

end DDNNFNeg.Supplement
