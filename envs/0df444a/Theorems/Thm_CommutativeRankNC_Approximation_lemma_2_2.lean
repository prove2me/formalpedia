-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_lemma_2_2
-- name    : CommutativeRankNC.Approximation.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:21.372166+00:00
-- url     : https://prove2.me/theorems/5f3f19bd-2839-48cd-965c-c71c2de58010
-- title:
--   Lemma 2.2 — Trace linearity, kernel and uniformity
-- statement:
--   In the binary extension field of order $q=2^{r_f}$ with $r_f=\lceil\log_2m\rceil\ge1$, let $\operatorname{Tr}(a)=\sum_{j<r_f}a^{2^j}$. This sum lies in $\{0,1\}$, the trace is $\mathbb F_2$-linear and nonzero, and
--
--   $$\operatorname{Tr}:\mathbb F_q\twoheadrightarrow\mathbb F_2,\quad|\ker\operatorname{Tr}|=2^{r_f-1}=q/2,\quad\Pr[\operatorname{Tr}(U)=b]=1/2\quad(b\in\mathbb F_2).$$
--
--   Here $U$ is uniform on all $q$ field representatives. Both additivity and scalar linearity are explicit. The result turns field-uniform values into unbiased bits.
--
--   Differences from the source:
--   - encoding: elements of the quotient field F₂[z]/(f) → binary coefficient representatives, finite trial division, and reduction modulo the first irreducible polynomial; reason: these are the explicit field representation and deterministic search in the proof of Lemma 2.1; no arithmetic oracle is used
--   - encoding: the trace of a uniformly distributed field element → the number of field representatives with each trace bit divided by q; reason: uniform probability on the finite field is exactly normalized counting; no sign distribution is involved
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Lemma 2.2, PDF/printed p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Signs

namespace CommutativeRankNC.Approximation

/-- Lemma 2.2, PDF/printed pp.9–10, all trace properties in binary field
coordinates. The final two clauses are the kernel size and pushforward law. -/
theorem lemma_2_2 (m : ℕ) (hm : 2 ≤ m) :
    (∀ a < fieldCard m, rawTrace m a = if traceBit m a then 1 else 0) ∧
    (∀ a < fieldCard m, ∀ b < fieldCard m,
      traceBit m (fieldAdd m a b) = Bool.xor (traceBit m a) (traceBit m b)) ∧
    (∀ a < fieldCard m, ∀ c : Bool,
      traceBit m (if c then a else 0) = (c && traceBit m a)) ∧
    (∃ a < fieldCard m, traceBit m a = true) ∧
    (∀ b : Bool, ∃ a < fieldCard m, traceBit m a = b) ∧
    ((Finset.range (fieldCard m)).filter (fun a => traceBit m a = false)).card =
      2 ^ (fieldDegree m - 1) ∧
    2 ^ (fieldDegree m - 1) = fieldCard m / 2 ∧
    ∀ b : Bool,
      (((Finset.range (fieldCard m)).filter (fun a => traceBit m a = b)).card : ℝ) /
        (fieldCard m : ℝ) = 1/2 := by sorry

end CommutativeRankNC.Approximation
