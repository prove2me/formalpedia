-- Prove2me | Theorems.Thm_DDNNFNeg_theorem_1_1
-- name    : DDNNFNeg.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:49.907223+00:00
-- url     : https://prove2.me/theorems/b79022b3-a9a8-4e39-a0e5-18ec92b1e70f
-- title:
--   Theorem 1.1 (Exponential Separation) — some $f$ has a d-DNNF of size $O(n)$ while every DNNF for $\neg f$ has size $2^{\Omega(n)}$
-- statement:
--   **Theorem 1.1** (Exponential Separation). There are constants $C, c > 0$ such that for infinitely many $n \in \mathbb N$ there is a function $f : \{0,1\}^n \to \{0,1\}$ with:
--
--   1. $f$ is computed by a d-DNNF of size at most $C n$;
--   2. every DNNF computing $\neg f$ has size at least $2^{c n}$.
--
--   The lower bound holds even if the representation of the complement need not be deterministic. Hence d-DNNF is not polynomially closed under negation.
--
--   **Formalization Note** "For infinitely many $n$" is written: for every $N$ there is $n \ge N$. Size is the number of gates of the circuit (a DAG), input gates included. The d-DNNF of clause 1 has literal input gates only, as in the paper. Clause 2 also covers DNNFs with constant leaves; this is needed, since no constant-free DNNF computes the constant $0$, so over constant-free DNNFs alone the statement would hold trivially for $f \equiv 1$.
--
--   Differences from the source:
--   - reading: for infinitely many n … of size O(n) … size 2^{Ω(n)} → ∃ C, c > 0 such that ∀ N ∃ n ≥ N with the bounds C·n and 2^{c·n}; reason: constants fixed before n is the only non-trivial reading: per-n constants make each single n a finite triviality
--   - generalization: every DNNF computing ¬f (literal input gates only) → every DNNF computing ¬f, constant leaves allowed; reason: a larger class; every constant-free DNNF is one, so it specializes to the paper's lower bound
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_Computes
import Definitions.Def_DDNNFNeg_NNF_IsConstFree
import Definitions.Def_DDNNFNeg_NNF_IsDDNNF

namespace DDNNFNeg

/-- **Theorem 1.1** (Exponential Separation) (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.3): for infinitely many `n ∈ ℕ`, there is a
function `f : {0,1}^n → {0,1}` such that `f` is computable by a d-DNNF of size `O(n)` but every
DNNF computing `¬f` has size `2^{Ω(n)}`.

**Formalization Note** The constants `C, c > 0` of `O(n)` and `2^{Ω(n)}` are fixed before
"for infinitely many `n`" (written `∀ N, ∃ n ≥ N`). The d-DNNF of clause (a) is in the paper's
class: constant-free (literal input gates), decomposable and deterministic, of size `≤ C n`
(gates counted, input gates included). Clause (b) quantifies over every DNNF, deterministic or
not, and also allows constant leaves; this larger class specializes to the paper's, and it is
needed: no constant-free DNNF computes the constant `0`, so over constant-free DNNFs alone the
statement would hold trivially for `f ≡ 1`. -/
theorem theorem_1_1 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, ∃ n ≥ N, ∃ f : (Fin n → Bool) → Bool,
      (∃ D : NNF (Fin n), D.IsConstFree ∧ D.IsDDNNF ∧ D.Computes f ∧ (D.size : ℝ) ≤ C * n) ∧
      (∀ D : NNF (Fin n), D.IsDNNF → D.Computes (fun x => !f x) →
        (2 : ℝ) ^ (c * n) ≤ (D.size : ℝ)) := by sorry

end DDNNFNeg
