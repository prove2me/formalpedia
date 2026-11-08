-- Prove2me | Theorems.Thm_ErrAmpOV_theorem_2_3
-- name    : ErrAmpOV.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:43.434987+00:00
-- url     : https://prove2.me/theorems/d5d24d9d-8756-40bd-9d21-6d7b1da7c3db
-- title:
--   Theorem 2.3 — deterministic reversible circuits for compaction
-- statement:
--   There are a constant $c\in\mathbb N$, giving $a(n)=cn$, a constant $C>0$ and a threshold $N_0$ such that for every $n\ge N_0$ there are a circuit $\mathsf{Route}_n$ and a map $b\mapsto\sigma_b$ from strings $b\in\{0,1\}^n$ to permutations of $[n]$ with the following properties, where $w=\sum_i b_i$.
--
--   1. $\mathsf{Route}_n$ has $a(n)$ output bits and at most $Cn\log n$ gates. If $b_i=0$ then $\sigma_b(i)\in\{1,\dots,n-w\}$, and if $b_i=1$ then $\sigma_b(i)\in\{n-w+1,\dots,n\}$.
--   2. For every $k\ge N_0$ there is a circuit $\mathsf{Com}_{n,k}$ with at most $Cnk$ gates such that on $A_\sigma=\mathsf{Route}_n(b)$ and any $x_1,\dots,x_n\in\{0,1\}^k$ it outputs
--   $$
--   x_{\sigma_b^{-1}(1)},\dots,x_{\sigma_b^{-1}(n)} .
--   $$
--   3. For every $k\ge N_0$ there is a circuit $\mathsf{UnCom}_{n,k}$ with at most $Cnk$ gates such that on $A_\sigma=\mathsf{Route}_n(b)$ and any $x'_1,\dots,x'_n\in\{0,1\}^k$ it outputs
--   $$
--   x'_{\sigma_b(1)},\dots,x'_{\sigma_b(n)} .
--   $$
--
--   So a list of key-payload pairs with one-bit keys can be sorted by key at a cost linear in the total payload size once the routing string is known, and the sort can be undone. This is what lets each amplification round pay only for the instances that still need work. The paper cites the theorem from Koucký–Král (ICALP 2021, Corollary 18), which is built on Pippenger's self-routing superconcentrators.
--
--   **Formalization Note** The output bits of $\mathsf{Com}$ and $\mathsf{UnCom}$ are in block order: bit $l$ of block $i$ is at position $ik+l$. Indices are 0-based.
--
--   Differences from the source:
--   - reading: a string A_σ ∈ {0,1}^{a(n)} that encodes a permutation σ → a map σ from key strings to permutations; Route_n(b) has length c·n, and Com, UnCom read it and route by σ_b for every payload x; reason: the encoding is what the Com and UnCom contracts use; one σ_b is shared by items 1–3 as on the page
--   - encoding: σ(i) ∈ {1, …, n − w} and {n − w + 1, …, n}, indices in [n] = {1, …, n} → σ b i < n − w and n − w ≤ σ b i on Fin n; reason: 0-based indices; w ≤ n, so the natural subtraction is exact
--   - reading: for every large enough n; for every large enough n, k; size O(n log(n)), O(n · k) → one threshold N₀ for n and for k, and one constant C with size ≤ C·n·log n, size ≤ C·n·k; reason: the maximum of the thresholds and of the constants of the three items
--   - encoding: Boolean circuits, no gate basis fixed, size = number of gates → ErrAmpOV.Circuit: constant, NOT, AND, OR gates of fan-in at most 2, unbounded fan-out, inputs not counted, a list of output wires; a read of a gate not yet computed returns false; reason: the basis is unspecified on the page; complete fan-in-2 bases differ by a constant factor, and the out-of-range read only gives a free constant false
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Theorem 2.3, p.7 (proof sketch in Appendix B, pp.26–27)

import Mathlib
import Definitions.Def_ErrAmpOV_Circuit

set_option autoImplicit false

namespace ErrAmpOV

/-- Theorem 2.3 (Deterministic reversible circuits for compaction), p.7, cited from [KK21,
Corollary 18]. There are a constant `c ∈ ℕ` (so `a(n) = c·n`), a constant `C > 0` and a threshold
`N₀` such that for every `n ≥ N₀` there are a circuit `Route_n` with `c·n` outputs and a map `σ`
from key strings `b ∈ {0,1}^n` to permutations of `{0, …, n-1}` with:

1. if `b_i = 0` then `σ_b(i) < n − w`, and if `b_i = 1` then `σ_b(i) ≥ n − w`, where `w = Σ b_i`;
   `Route_n` has size at most `C·n·log n`;
2. for every `k ≥ N₀` a circuit `Com_{n,k}` of size at most `C·n·k`, which on the routing string
   `A_σ = Route_n(b)` and items `x_0, …, x_{n-1} ∈ {0,1}^k` outputs `x_{σ_b⁻¹(0)}, …, x_{σ_b⁻¹(n-1)}`;
3. for every `k ≥ N₀` a circuit `UnCom_{n,k}` of size at most `C·n·k`, which on `A_σ = Route_n(b)`
   and `x'_0, …, x'_{n-1}` outputs `x'_{σ_b(0)}, …, x'_{σ_b(n-1)}`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Theorem 2.3, p.7 (proof sketch in Appendix B, pp.26–27).

**Formalization Note.**
* "`A_σ` encodes a permutation `σ`" is read as: `σ` is a function of the key string `b`, and
  `Route_n(b)` is a string of length `c·n` from which `Com` and `UnCom` route by `σ_b`. One `σ_b`
  is shared by items 1–3, and `Com`, `UnCom` are correct for every payload on every routing
  string `Route_n(b)`.
* Indices are 0-based: the page's `σ(i) ∈ {1, …, n − w}` becomes `σ_b(i) < n − w`.
* `O(n log n)` and `O(n·k)` are `≤ C·n·log n`, `≤ C·n·k` with one `C`; "for every large enough
  `n`" and "for every large enough `n, k`" are one threshold `N₀`. `log` is `Real.log`.
* Items are `Fin n × Fin k` input bits; output position `finProdFinEquiv (i, l) = i·k + l` is bit
  `l` of output block `i`. -/
theorem theorem_2_3 :
    ∃ (c : ℕ) (C : ℝ) (N₀ : ℕ), 0 < C ∧ ∀ n ≥ N₀,
      ∃ (Route : Circuit (Fin n)) (σ : (Fin n → Bool) → Equiv.Perm (Fin n)),
        Route.outs.length = c * n ∧ (Route.size : ℝ) ≤ C * n * Real.log n ∧
        (∀ (b : Fin n → Bool) (i : Fin n),
          (b i = false → (σ b i : ℕ) < n - (Finset.univ.filter (fun j => b j = true)).card) ∧
          (b i = true → n - (Finset.univ.filter (fun j => b j = true)).card ≤ (σ b i : ℕ))) ∧
        ∀ k ≥ N₀, ∃ Com UnCom : Circuit (Fin (c * n) ⊕ (Fin n × Fin k)),
          (Com.size : ℝ) ≤ C * n * k ∧ (UnCom.size : ℝ) ≤ C * n * k ∧
          Com.outs.length = n * k ∧ UnCom.outs.length = n * k ∧
          ∀ (b : Fin n → Bool) (x : Fin n × Fin k → Bool) (i : Fin n) (l : Fin k),
            (Com.eval (Sum.elim (fun q : Fin (c * n) => (Route.eval b).getD (q : ℕ) false) x)).getD
                (finProdFinEquiv (i, l) : ℕ) false = x ((σ b).symm i, l) ∧
            (UnCom.eval (Sum.elim (fun q : Fin (c * n) => (Route.eval b).getD (q : ℕ) false) x)).getD
                (finProdFinEquiv (i, l) : ℕ) false = x (σ b i, l) := by sorry

end ErrAmpOV
