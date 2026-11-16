-- Prove2me | Theorems.Thm_EnumeratingComplexity224_Dichotomy_Supplement_transfer
-- name    : EnumeratingComplexity224.Dichotomy.Supplement.transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:31:46.205259+00:00
-- url     : https://prove2.me/theorems/89cb30b9-9cce-4405-a219-7a097463fac2
-- title:
--   Theorem 2 (Transfer) — computable bounds from finite sets to infinite sets
-- statement:
--   Fix the optimal deterministic and randomized enumeration machines defining $D$ and $R$ as in Definitions 7 and 9. Here $D(A)$ is the length of a shortest finite program that enumerates exactly $A\subseteq\mathbb N$, or $\infty$ if none exists, and $R(A)$ is the probability of enumerating exactly $A$ over an infinite fair binary tape.
--
--   Let $f:\mathbb N\to\mathbb N$ be total computable and non-decreasing. Suppose the same $f$ satisfies, for every $k\in\mathbb N$ and every finite $F\subseteq\mathbb N$,
--
--   $$R(F)\ge 2^{-k}\quad\Longrightarrow\quad D(F)<f(k).$$
--
--   Define $h(k)=\min\{n\in\mathbb N:k^2\le 2^n\}$. Thus $h(k)=\lceil2\log_2 k\rceil$ for $k\ge1$, and $h(0)=0$. There is a natural constant $C$, depending only on $f$ and the fixed machines, such that for every $k\in\mathbb N$ and every infinite $S\subseteq\mathbb N$,
--
--   $$R(S)\ge 2^{-k}\quad\Longrightarrow\quad D(S)<f(k+h(k)+C).$$
--
--   This transfers every computable monotone strict finite-set bound to all infinite sets with the stated exact logarithmic argument shift. The constant is chosen before both $k$ and $S$. No computable-enumerability hypothesis is imposed on $S$.
--
--   Differences from the source:
--
--   - encoding: fixed optimal deterministic and randomized machines defining D and R → parameters m and p with the published OptimalDeterministic and OptimalRandom predicates; D in ℕ∞ and R in ENNReal; reason: retains the published append-only infinite-time enumeration model and all optimal-machine choices; a finite natural bound is cast into ℕ∞ and the positive dyadic threshold into ENNReal
--   - encoding: k + ⌈2 log₂ k⌉ + C, with rounding specified on p.11 → k + Nat.clog 2 (k ^ 2) + C; reason: Nat.clog 2 (k ^ 2) is the least n with k² ≤ 2ⁿ and equals the ceiling of the entire doubled binary logarithm for k ≥ 1; the local verification module proves the equivalence
--   - encoding: all natural k with an implicit logarithm endpoint convention → all k : ℕ, with Nat.clog 2 (0 ^ 2) = 0; reason: k=0 satisfies the k=1 probability threshold; increasing the one uniform C by 1 covers k=0 and preserves every positive-k instance by monotonicity, as proved in the local verification module
-- source:
--   Alexander Shekhovtsov, Nikolay Vereshchagin, Georgii Zakharov, Enumerating Complexity Revisited, STOC 2027 submission #224 (October 2026), p. 3, Theorem 2 (Transfer); p. 11, §4 proof and exact rounding convention; pp. 5–6, Definitions 7 and 9 and standing conventions. PDF SHA-256 2c18f5688bb212b4cc7cec401c89f1a9ecace957b95e3f574d72438d9f1859b1

import Definitions.Def_EnumeratingComplexity224_Dichotomy_Machines

namespace EnumeratingComplexity224.Dichotomy.Supplement

/-- Theorem 2 (Transfer), p.3; the exact rounding is specified on p.11.
`Nat.clog 2 (k ^ 2)` is the least n with k² ≤ 2ⁿ. For positive k this
is ⌈2 log₂ k⌉; at zero it is zero. No normalization of the optimal
machines and no effective-enumerability assumption on S are imposed. -/
theorem transfer (m p : Machine)
    (hm : OptimalDeterministic m) (hp : OptimalRandom p)
    (f : ℕ → ℕ) (hf : Computable f) (hmono : Monotone f)
    (hfinite : ∀ (k : ℕ) (F : Set ℕ), F.Finite →
      ENNReal.ofReal (dyadic k) ≤ probability p F [] →
      complexity m F < (f k : ℕ∞)) :
    ∃ C : ℕ, ∀ (k : ℕ) (S : Set ℕ), S.Infinite →
      ENNReal.ofReal (dyadic k) ≤ probability p S [] →
      complexity m S < (f (k + Nat.clog 2 (k ^ 2) + C) : ℕ∞) := by sorry

end EnumeratingComplexity224.Dichotomy.Supplement
