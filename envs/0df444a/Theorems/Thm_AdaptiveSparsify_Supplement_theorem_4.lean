-- Prove2me | Theorems.Thm_AdaptiveSparsify_Supplement_theorem_4
-- name    : AdaptiveSparsify.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:54:37.547842+00:00
-- url     : https://prove2.me/theorems/00366959-3ad9-48ba-95c2-496f4996db03
-- title:
--   Theorem 4 — one-pass $\tilde O(nd)$ reduction from boxed LP feasibility with margin $\xi$ to an integer minimum enclosing ball radius gap
-- statement:
--   There are one program $P$ of the deterministic one-pass integer RAM and constants $C>0$, $k\in\mathbb N$ such that the following holds.
--
--   Let $n\ge d\ge1$ and $B\ge1$, let $A\in\mathbb Z^{n\times d}$ and $b\in\mathbb Z^n$, and let $U\ge0$ and $\xi>0$ be integers, all entries of $A$ and $b$ and $U,\xi$ having absolute value below $2^B$. On the input stream $n,d,B,U,\xi,a_1,b_1,\dots,a_n,b_n$, the run of $P$
--
--   1. halts without fault after at most $C\,nd\,\big(B\max(1,\log_2 n)\big)^k$ instructions;
--   2. holds at every step only integers of fewer than $C\,B\max(1,\log_2 n)$ bits;
--   3. outputs $m\le C(n+d)$ points $p_1,\dots,p_m\in\mathbb Z^D$ with $D\le Cd$, and integers $\theta$ and $\varrho>0$, all of fewer than $C\,B\max(1,\log_2 n)$ bits, such that
--      - if $Ax\le b$, $-U\mathbf 1\le x\le U\mathbf 1$ has a solution $x\in\mathbb R^d$, then the minimum enclosing ball of the points has radius at most $\theta$;
--      - if $Ax\le b+\xi\mathbf 1$, $-U\mathbf 1\le x\le U\mathbf 1$ has no solution $x\in\mathbb R^d$, then the minimum enclosing ball of the points has radius at least $\theta+\varrho$.
--
--   So deciding the radius of a minimum enclosing ball to within an additive integer gap is as hard as robust feasibility of a boxed linear program, by a reduction of nearly linear size and time. This is the complement of the paper's $\tilde O(nd+d^6\sqrt n)$ algorithm for minimum enclosing ball (Corollary 1.1).
--
--   **Formalization Note** The radius of the minimum enclosing ball is $\min_{c\in\mathbb R^D}\max_\ell\|p_\ell-c\|_2$ over real centres.
--
--   Differences from the source:
--   - reading: "we can create … in one pass over the input" → one program of the deterministic integer RAM whose input stream n, d, B, U, ξ, a_1, b_1, …, a_n, b_n is readable only through next (each integer read at most once, in order); output written as the stream m, D, θ, ϱ, p_1, …, p_m; reason: the header comes first so that Λ = 4d2^B, U and ξ are known before the rows (Algorithm 3, p.60); the program may store what it reads
--   - reading: Õ(nd) arithmetic operations, under the unit-cost convention on O(B log n)-bit integers (p.55) → work ≤ C n d (B max(1, log₂ n))^k counting every instruction, and every integer held in any register or memory cell at every step has fewer than C B max(1, log₂ n) bits; reason: the radical rounding of Definition 8.7 costs O(B log n) operations per coordinate (p.55); the bit bound on all held integers is what makes unit cost meaningful
--   - reading: m = O(n + d), O(d) dimensions, O(B log n) bits → m ≤ C(n + d), D ≤ C d, |p_{ℓk}|, |θ|, |ϱ| < 2^{C B max(1, log₂ n)}, with C, k chosen before the input; reason: every O(·) gets one explicit constant fixed before the input; log n is read as max(1, log₂ n) as stated on p.55
--   - reading: integers with B bits → |x| < 2^B, with B ≥ 1 known (it is in the input), d ≥ 1, U ≥ 0; reason: the conventions stated on p.55
--   - encoding: the minimum enclosing ball has radius at most θ / at least θ + ϱ → some centre c ∈ ℝ^D has ‖p_ℓ − c‖₂ ≤ θ for all ℓ / every centre has some ℓ with ‖p_ℓ − c‖₂ ≥ θ + ϱ; reason: the minimum over centres is attained, so these are rad(P) ≤ θ and rad(P) ≥ θ + ϱ, with no infimum junk value
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Theorem 4, p.55 (also p.9); conventions p.55; proof §8, pp.55–61 (Algorithm 3, Lemma 8.9)

import Mathlib
import Definitions.Def_AdaptiveSparsify_Supplement_IntRAM
import Definitions.Def_AdaptiveSparsify_Supplement_MEBReduction

namespace AdaptiveSparsify

namespace Supplement

/-- **Theorem 4**, p.55 (also printed on p.9); proof §8, pp.55–61.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Theorem 4, p.55.

"Given linear constraints Ax ≤ b with a bounding box −U1 ≤ x ≤ U1 and error margin ξ > 0, where A is
n-by-d with n ≥ d, and the entries of A and b, as well as U and ξ, are integers with B bits, we can
create in one pass over the input and in Õ(nd) arithmetic operations, a set of m = O(n + d) points
p_1 … p_m in O(d) dimensions, as well as a threshold θ and gap ϱ > 0, all of which are integers with
O(B log n) bits, such that: If Ax ≤ b, −U1 ≤ x ≤ U1 is feasible, the minimum enclosing ball of the
points has radius at most θ. If Ax ≤ b + ξ1, −U1 ≤ x ≤ U1 is infeasible, the minimum enclosing ball
of the points has radius at least θ + ϱ."

**Formalization Note.** Deterministic: one program `P` of the one-pass integer RAM
(`AdaptiveSparsify.Supplement.IntRAM`) and constants `C`, `k` chosen before the input. The conventions of
p.55: `d ≥ 1`, `U ≥ 0`, `B ≥ 1` known (it is in the input stream), `log n` read as `max(1, log₂ n)`,
unit cost on `O(B log n)`-bit integers — enforced by bounding every integer held in a register or
memory cell at every step by `C · B · max(1, log₂ n)` bits. `Õ(nd)` is `C n d (B max(1, log₂ n))^k`
(the radical rounding of Definition 8.7 costs `O(B log n)` operations per coordinate, p.55). -/
theorem theorem_4 :
    ∃ P : Supplement.IntProgram, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n d B : ℕ) (A : Matrix (Fin n) (Fin d) ℤ) (b : Fin n → ℤ) (U ξ : ℤ),
        1 ≤ d → d ≤ n → 1 ≤ B → 0 ≤ U → 0 < ξ →
        (∀ i j, |A i j| < 2 ^ B) → (∀ i, |b i| < 2 ^ B) → |U| < 2 ^ B → |ξ| < 2 ^ B →
        ∃ t : ℕ,
          (Supplement.intRun P (Supplement.lpStream A b B U ξ) t).halted = true ∧
          (Supplement.intRun P (Supplement.lpStream A b B U ξ) t).faulted = false ∧
          ((Supplement.intRun P (Supplement.lpStream A b B U ξ) t).work : ℝ) ≤
            C * n * d * ((B : ℝ) * max 1 (Real.logb 2 n)) ^ k ∧
          (∀ t' ≤ t, (Supplement.intRun P (Supplement.lpStream A b B U ξ) t').HeldBelow
            (Supplement.bitBound C B n)) ∧
          ∃ (m D : ℕ) (p : Fin m → Fin D → ℤ) (θ ϱ : ℤ),
            (Supplement.intRun P (Supplement.lpStream A b B U ξ) t).output =
              Supplement.mebStream p θ ϱ ∧
            (m : ℝ) ≤ C * ((n : ℝ) + d) ∧ (D : ℝ) ≤ C * d ∧ 0 < ϱ ∧
            (∀ l q, ((|p l q| : ℤ) : ℝ) < Supplement.bitBound C B n) ∧
            ((|θ| : ℤ) : ℝ) < Supplement.bitBound C B n ∧
            ((|ϱ| : ℤ) : ℝ) < Supplement.bitBound C B n ∧
            (Supplement.BoxFeasible A b U 0 → Supplement.MEBRadiusLE p θ) ∧
            (¬ Supplement.BoxFeasible A b U ξ → Supplement.MEBRadiusGE p ((θ : ℝ) + ϱ)) := by sorry

end Supplement

end AdaptiveSparsify
