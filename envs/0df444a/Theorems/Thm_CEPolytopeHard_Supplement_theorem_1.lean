-- Prove2me | Theorems.Thm_CEPolytopeHard_Supplement_theorem_1
-- name    : CEPolytopeHard.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:13:08.876204+00:00
-- url     : https://prove2.me/theorems/8556faa9-b122-42ec-bf51-7a5d794d9ffd
-- title:
--   Theorem 1 — computing a $d^{-c}$-fixed set with at most $d^C$ points of a Lipschitz map is PPAD-hard
-- statement:
--   Let $f:[0,1]^d\to[0,1]^d$ be a map. An **$\epsilon$-fixed set** of $f$ (Definition 3.2) is a finite set $S=\{x_1,\dots,x_k\}\subseteq[0,1]^d$ together with a Markov chain $P$ on $[k]$ and a stationary distribution $\mu$ of $P$ such that
--   $$\mathbb E_{i\sim\mu}\Big\|x_i-\mathbb E_{j\sim P(i)}f(x_j)\Big\|_2\le\epsilon ,$$
--   with the normalized norm $\|v\|_2=\big(\tfrac1d\sum_i v_i^2\big)^{1/2}$.
--
--   **Theorem 1.** There is an absolute constant $L$ such that for every fixed $C\ge1$ there is a constant $c>0$ for which the following problem is PPAD-hard: given an $L$-Lipschitz map $f:[0,1]^d\to[0,1]^d$ represented by an arithmetic circuit (so that it can be evaluated in polynomial time), compute a $d^{-c}$-fixed set $S$ of $f$ with
--   $$|S|\le d^{C}.$$
--
--   Fixed points are fixed sets with one point, so the problem is at most as hard as computing an approximate Brouwer fixed point; the theorem shows that, at accuracy polynomially small relative to the support bound, it is not easier. It is the source of the correlated-equilibrium hardness results of Theorems 2 and 4.
--
--   **Formalization Note** The problem is `fixedSetProblem L C c`; PPAD-hardness is the mission's `PPADHard`.
--
--   Differences from the source:
--   - encoding: PPAD-hard (not defined in the paper) → PPADHard (the mission's published definition: every problem of QuasiStrictNE.PPAD reduces by CardinalMatching.SearchReduces); reason: standard Levin search reductions on Cook's machines, as in the base mission
--   - reading: "given a Lipschitz function f : [0,1]^d → [0,1]^d" → ∃ L (an absolute Lipschitz constant) before ∀ C; instances are L-Lipschitz on [0,1]^d in the normalized norm; reason: the proof takes L absolute from [72] (p.15: "even when L ≥ 1 and 0 < δ ≤ 1 are absolute constants"); hardness for a fixed L implies hardness for "some Lipschitz constant", so this is the stronger reading
--   - reading: "can be evaluated in polynomial time"; Section 2.1: functions are arithmetic circuits with standard gates, rationals in binary → a valid well-behaved NadlerCLS.Circ with d inputs and d outputs, instance code encNat d ++ encCirc F, promise f([0,1]^d) ⊆ [0,1]^d; reason: Section 2.1's representation; well-behavedness (true-multiplication depth ≤ log₂ size) is the standard condition making circuits evaluable in polynomial time; it narrows the instance class, so the hardness claim is not weakened
--   - encoding: dimension d (implicitly ≥ 1) → 0 < d in the validity of an instance; reason: at d = 0 the bound |S| ≤ 0^C = 0 admits no fixed set; the exclusion removes only this undefined case
--   - encoding: a d^{−c}-fixed set S with |S| ≤ d^C (Definition 3.2) → a list of rational vectors of length d, merged into a Finset S; card S ≤ (d:ℝ)^C and IsFixedSet (Icc 0 1) f ((d:ℝ)^(−c)) S with the normalized norm; reason: Section 2.1's output form; Definition 3.2 uses the normalized norm of Sections 3–4
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Theorem 1, p.3, restated p.15; proof pp.15–19

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_CEPolytopeHard_Supplement_fixedSetProblem

set_option autoImplicit false

namespace CEPolytopeHard.Supplement

/-- **Theorem 1** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of
Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2,
2026, sha256 6aec500a…7820, Theorem 1, p.3, restated p.15 and proved pp.15–19): "For every fixed
C ≥ 1, there is a constant c > 0 such that the following problem is PPAD-hard: given a Lipschitz
function f : [0, 1]^d → [0, 1]^d that can be evaluated in polynomial time, compute a
d^{−c}-fixed set S of f with |S| ≤ d^C."

**Formalization Note** "Lipschitz" is read with an absolute Lipschitz constant `L`, chosen
before `C` (the proof takes `L` from the cited Brouwer hardness, p.15: "even when L ≥ 1 and
0 < δ ≤ 1 are absolute constants"); this is the stronger reading. "Evaluated in polynomial time"
is the circuit representation of Section 2.1 (valid well-behaved arithmetic circuits).
PPAD-hardness is `PPADHard`; the problem is `fixedSetProblem L C c`. -/
theorem theorem_1 :
    ∃ L : ℝ, ∀ C : ℝ, 1 ≤ C → ∃ c : ℝ, 0 < c ∧ PPADHard (fixedSetProblem L C c) := by sorry

end CEPolytopeHard.Supplement
