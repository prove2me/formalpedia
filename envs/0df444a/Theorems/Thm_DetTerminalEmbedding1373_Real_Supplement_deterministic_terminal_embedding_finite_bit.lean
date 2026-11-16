-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_Supplement_deterministic_terminal_embedding_finite_bit
-- name    : DetTerminalEmbedding1373.Real.Supplement.deterministic_terminal_embedding_finite_bit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:17:52.322542+00:00
-- url     : https://prove2.me/theorems/d265992c-ec13-451a-b792-473aa01e3a1e
-- title:
--   Theorem 1.3 — deterministic terminal embedding, finite-bit version
-- statement:
--   There are two fixed deterministic bit machines, a preprocessing machine $P$ and a query machine $Q$ (multi-stack Turing machines with finite alphabets reading and writing bits), and a constant $C$, such that the following holds for all inputs.
--
--   Let $x_1,\dots,x_n\in\mathbb Q^d$ ($n\ge1$) be distinct points whose coordinates have height at most $B$, let $\varepsilon\in\mathbb Q$ with $0<\varepsilon\le 1/2$ and height at most $B_\varepsilon$, and let $S$ be an integer with $2\le S\le(\varepsilon/12)^{-2}$. On the binary encoding of $(x_1,\dots,x_n,\varepsilon,S)$ the machine $P$ halts and writes a bit string $D$; for every $q\in\mathbb Q^d$, $Q$ halts on $(D,q)$ and writes a vector $F(q)\in\mathbb Q^m$, where $m$ is the same for all $q$. The map $F:\mathbb Q^d\to\mathbb Q^m$ so computed, terminals included, satisfies:
--
--   1. **Distortion.** For every terminal $x_i$ and every query $q\in\mathbb Q^d$,
--   $$(1-\varepsilon)\|q-x_i\|\le\|F(q)-F(x_i)\|\le(1+\varepsilon)\|q-x_i\|.$$
--   2. **Target dimension.** $m\le C\bigl(1+\tfrac{\varepsilon^{-4}}{S}\log\max(n,2)\bigr)$, that is, $m=O\bigl((\varepsilon^{-4}/S)\log n\bigr)$.
--   3. **Preprocessing time.** $P$ halts within $C\max(n,2)^{C S}\,(d+B+B_\varepsilon+\lceil1/\varepsilon\rceil+2)^C$ steps, that is, $n^{O(S)}\operatorname{poly}(d,B,B_\varepsilon,1/\varepsilon)$.
--   4. **Query time.** For every $B_q$ bounding the heights of the coordinates of $q$, $Q$ halts on $(D,q)$ within $C\,(n+d+B+B_q+B_\varepsilon+\lceil1/\varepsilon\rceil+2)^C$ steps, that is, $\operatorname{poly}(n,d,B,B_q,B_\varepsilon,1/\varepsilon)$.
--
--   Norms are Euclidean norms of the real points. This is the finite-precision counterpart of the real-arithmetic Theorem 1.1: rational terminals and queries, a rational output, the same $1\pm\varepsilon$ guarantee and the same dimension–time tradeoff in $S$, with costs counted in bit operations.
--
--   Differences from the source:
--   - encoding: O(·), n^{O(S)} and poly(·) bounds → one constant C chosen before all inputs, with the explicit shapes C·max(n,2)^{C·S}·(d+B+B_ε+⌈1/ε⌉+2)^C, C·(1+ε⁻⁴S⁻¹·log max(n,2)) and C·(n+d+B+B_q+B_ε+⌈1/ε⌉+2)^C; reason: this is the standard uniform reading of the asymptotic bounds; the additive 1 and max(n,2) only cover n = 1, since for n ≥ 2 and S ≤ (ε/12)⁻² one has ε⁻⁴S⁻¹ log n ≥ (log 2)/36
--   - reading: "there is a deterministic algorithm" in the bit-operation model → one fixed pair of Mathlib multi-stack Turing machines with finite stack alphabets (preprocessing on the binary encoding of (x, ε, S), then query on the stored string D and q), the same pair for every ε and S ("for every integer S … there is an algorithm" becomes one algorithm taking S as input), time = number of machine steps; reason: the paper fixes no machine model and its two-phase algorithm (§7.4) preprocesses once and then answers each query; step counts of such machines and bit-operation counts differ polynomially, which the poly(·) and n^{O(S)} classes absorb; the exponent O(S) has a meaning only with a constant independent of S, and §7.4 runs one algorithm with S as a parameter
--   - reading: F(x_i) of the terminal → the query machine's output on q = x_i; reason: F is one map on ℚᵈ, and §7.4 sets F̂(x_i) to the stored terminal image
--   - reading: height of a nonzero rational → the same condition |p|, q ≤ 2^B applied to every rational, so 0 = 0/1 has height at most every B; reason: §1.1 defines the height only for nonzero rationals, and zero coordinates are allowed inputs
--   - encoding: X = {x_1, …, x_n} a set of distinct points → an injective family indexed by Fin n with n ≥ 1; reason: log n and the terminal list require a nonempty set
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), p. 4, Theorem 1.3 (height defined on p. 4; proof in §7, pp. 23–31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Mathlib
import Definitions.Def_DetTerminalEmbedding1373_Real_Supplement_bitModel

set_option autoImplicit false

namespace DetTerminalEmbedding1373.Real.Supplement

/-- Theorem 1.3, p. 4 (proof §7, pp. 23–31). One fixed pair of deterministic bit machines
(preprocessing `P`, query `Q`) and one constant `C`, chosen before every input. On terminals
`x₁, …, xₙ ∈ ℚᵈ` (distinct, coordinates of height `≤ B`), a rational `0 < ε ≤ 1/2` of height `≤ B_ε`
and an integer `2 ≤ S ≤ (ε/12)⁻²`, `P` writes the stored data `D` within
`C·max(n,2)^{C·S}·(d + B + B_ε + ⌈1/ε⌉ + 2)^C` steps; the map `F : ℚᵈ → ℚᵐ` is what `Q` outputs on
`(D, q)`, terminals included; `m = O((ε⁻⁴/S) log n)`; each query of coordinate height `≤ B_q` takes
at most `C·(n + d + B + B_q + B_ε + ⌈1/ε⌉ + 2)^C` steps; and `F` has distortion `1 ± ε` between
every query and every terminal. -/
theorem deterministic_terminal_embedding_finite_bit :
    ∃ (P Q : Turing.TM2ComputableAux Bool Bool),
      RevRedSAT.FiniteAlphabets P ∧ RevRedSAT.FiniteAlphabets Q ∧
    ∃ C : ℕ,
    ∀ (n d : ℕ), 0 < n → ∀ (x : Fin n → Fin d → ℚ), Function.Injective x →
    ∀ B : ℕ, (∀ i, VecHeightLE (x i) B) →
    ∀ (ε : ℚ) (Bε : ℕ), 0 < ε → ε ≤ 1 / 2 → HeightLE ε Bε →
    ∀ S : ℕ, 2 ≤ S → (S : ℚ) ≤ ((ε / 12) ^ 2)⁻¹ →
    ∃ (m : ℕ) (D : List Bool) (F : (Fin d → ℚ) → (Fin m → ℚ)),
      HMBinPacking.OutputsWithin P (preprocessingInput x ε S) D
        (C * (max n 2) ^ (C * S) * (d + B + Bε + ⌈ε⁻¹⌉₊ + 2) ^ C) ∧
      (m : ℝ) ≤ (C : ℝ) * (1 + ((ε : ℝ)⁻¹ ^ 4 / (S : ℝ)) * Real.log ((max n 2 : ℕ) : ℝ)) ∧
      (∀ (q : Fin d → ℚ) (Bq : ℕ), VecHeightLE q Bq →
        HMBinPacking.OutputsWithin Q (queryInput D q) (vecBits (F q))
          (C * (n + d + B + Bq + Bε + ⌈ε⁻¹⌉₊ + 2) ^ C)) ∧
      ∀ (i : Fin n) (q : Fin d → ℚ),
        (1 - (ε : ℝ)) * ‖toE q - toE (x i)‖ ≤ ‖toE (F q) - toE (F (x i))‖ ∧
        ‖toE (F q) - toE (F (x i))‖ ≤ (1 + (ε : ℝ)) * ‖toE q - toE (x i)‖ := by sorry

end DetTerminalEmbedding1373.Real.Supplement
