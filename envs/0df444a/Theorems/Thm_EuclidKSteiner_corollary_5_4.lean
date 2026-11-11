-- Prove2me | Theorems.Thm_EuclidKSteiner_corollary_5_4
-- name    : EuclidKSteiner.corollary_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:33.393847+00:00
-- url     : https://prove2.me/theorems/c9268463-1c69-4ede-a644-b046c8d81ce0
-- title:
--   Corollary 5.4 — strings with prescribed zeros and ones: $s^{O(r)}\log n$ strings
-- statement:
--   There are a deterministic real-RAM program and a constant $C>0$ such that for all integers $n,s\ge2$ and $r\ge1$, on input $(n,s,r)$ the program halts within $C\,s^{Cr}\log_2 n\,(n+s+r)^C$ steps and outputs a family $X\subseteq\{0,1\}^n$ of at most $C\,s^{Cr}\log_2 n$ strings such that for all disjoint position sets $Z_0,Z_1\subseteq\{0,\dots,n-1\}$ with $|Z_0|+|Z_1|\le s$ and $|Z_1|\le r$, some string of $X$ is zero on $Z_0$ and one on $Z_1$.
--
--   Applied with $s=\lceil1+r\log n\rceil$ it yields the $2^{O(r\log r)}n^{O(1)}$ colorings used by Theorem 3.8.
--
--   **Formalization Note** The machine is the published real RAM restricted to admissible programs. The output is $N$ followed by each string as $n$ cells in $\{0,1\}$; repeated strings are allowed.
--
--   Differences from the source:
--   - encoding: one can deterministically construct X of size at most s^{O(r)} log n; its enumeration takes this bound times a polynomial in n + s + r → an admissible MatMulTimeLP.RealRAM program and C > 0 fixed before (n, s, r), halting with t + 1 ≤ C·s^{C·r}·log₂ n·(n + s + r)^C and outputting at most C·s^{C·r}·log₂ n strings (stringLayout, encodeStrings); reason: O-notation with the constants before the input; the real-RAM model of p.3
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Corollary 5.4, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_EuclidKSteiner_Layouts

namespace EuclidKSteiner

/-- **Corollary 5.4 (Strings with prescribed zeros and ones).** Bhore, Kisfaludi-Bak, Marx, Odak,
*Parameterized Tractability of Euclidean k-Steiner Tree*, STOC 2027 submission (manuscript sha256
75361687…), Corollary 5.4, p.23 (PDF p.25): "For integers n, s ≥ 2 and r ≥ 1, one can
deterministically construct a family X ⊆ {0, 1}^n such that every pair of disjoint position sets
Z_0, Z_1, with |Z_0| + |Z_1| ≤ s and |Z_1| ≤ r, is realized by a string that is zero on Z_0 and one on
Z_1. The family has size at most s^{O(r)} log n. Its enumeration takes this bound times a polynomial
in n + s + r."

There are an admissible real-RAM program and `C > 0` such that for all `n, s ≥ 2`, `r ≥ 1` and every
tape, on input `(n, s, r)` the run halts at a step `t` with
`t + 1 ≤ C · s^{C r} · log₂ n · (n + s + r)^C` and outputs a list `X` of strings in `{0,1}^n` with
`|X| ≤ C · s^{C r} · log₂ n` such that for all disjoint `Z₀, Z₁ ⊆ {0, …, n − 1}` with
`|Z₀| + |Z₁| ≤ s` and `|Z₁| ≤ r` some string of `X` is `0` on `Z₀` and `1` on `Z₁`.

**Formalization Note** The output is `N`, then each string as `n` cells in `{0, 1}`
(`encodeStrings`); duplicate strings are allowed, as on the page. `log₂ n ≥ 1` since `n ≥ 2`. -/
theorem corollary_5_4 :
    ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n s r : ℕ), 2 ≤ n → 2 ≤ s → 1 ≤ r → ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ,
        MatMulTimeLP.HaltsAt A (stringLayout n s r) ω t ∧
        (t : ℝ) + 1 ≤ C * (s : ℝ) ^ (C * r) * Real.logb 2 n * ((n : ℝ) + s + r) ^ C ∧
        ∃ X : List (Fin n → Bool), OutputIs A (stringLayout n s r) ω t (encodeStrings X) ∧
          (X.length : ℝ) ≤ C * (s : ℝ) ^ (C * r) * Real.logb 2 n ∧
          ∀ Z₀ Z₁ : Finset (Fin n), Disjoint Z₀ Z₁ → Z₀.card + Z₁.card ≤ s → Z₁.card ≤ r →
            ∃ x ∈ X, (∀ j ∈ Z₀, x j = false) ∧ ∀ j ∈ Z₁, x j = true := by sorry

end EuclidKSteiner
