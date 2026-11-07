-- Prove2me | Theorems.Thm_BddExp3SUM_eq_14_to_16
-- name    : BddExp3SUM.eq_14_to_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:01:16.068761+00:00
-- url     : https://prove2.me/theorems/c2f98ed0-2790-413b-8cba-7b57402b6381
-- title:
--   (14)–(16): the legal matrix call and the cost chain $N^2/D^\gamma=O_M(n^2R^{-\gamma/2})$, down to $n^{2-\delta_M}$
-- statement:
--   Let $M\ge2$. There is a constant $C$ depending only on $M$ such that for all $n\ge16$ with $R\ge M$, and every prime $p\mid M$ and $q$ with $R/M<D=p^q\le R$:
--
--   The call is legal: $N\ge g_0n\sqrt D/\sigma\ge n$, $D\le R\le n^\eta\le N^{1/18}$, $D^{18}\le N$, $D^{1+\gamma}\le N$, the number $(M^2+1)n/\sigma$ of blocks is at most $g'$, the cap satisfies $\lceil An^2/\sigma\rceil\le(A+1)n^2/\sigma$, and
--
--   $$\frac{N^2}{\sqrt D}\ge\frac{g_0^2n^2\sqrt D}{\sigma^2}\ge\frac{g_0^2}{\sqrt M}\frac{n^2}{\sigma}\ge(A+1)\frac{n^2}{\sigma}.$$
--
--   The costs fit: $p^{\lceil q/2\rceil}\le\sqrt{pD}$, $g'\le(g_0+1)n/\sigma$, and with $C$-multiples
--
--   $$N^2/D^\gamma\lesssim n^2R^{1-\gamma}/\sigma^2\lesssim n^2R^{-\gamma/2},$$
--
--   the terms $ND$, $n\sqrt{pD}$, $n^2/\sigma$ and $\sigma^2n^2/R+\sigma$ are all at most $Cn^2R^{-\gamma/2}$, and $n^2R^{-\gamma/2}\le Cn^{2-\delta_M}$.
--
--   This is the arithmetic that turns the construction into the exponent of Theorem 1.
--
--   Differences from the source:
--   - generalization: p ∣ e, q = ⌊log_p R⌋ from a certificate → any prime p ∣ M and any q with R/M < p^q ≤ R; reason: these are the only properties the chain uses; the source’s p and q satisfy them
--   - encoding: O_M(·), O_{M,c}(·) polylog n in (15), (16) → one constant C depending only on M, before n, p, q; the common factor polylog n is left out; reason: the polylog factor multiplies both sides; the cost sentences themselves are carried by the goal theorem
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), (14)–(16), pp.6–7 (PDF pp.7–8); parameters p.5

import Mathlib
import Definitions.Def_BddExp3SUM_Blocks

namespace BddExp3SUM

/-- The legal matrix call and the cost chain (14)–(16), pp.6–7 (Zeng, Wang, Cao, Dai, Wang, STOC 2027
submission, manuscript sha256 19546c9a…).

**Formalization Note.** All in `ℝ`. `C` is the constant of `O_M`: it depends on `M` only, not on `n`, `p`
or `q`. The common factor `polylog n` of (16) is left out. The last clause is the step from `R^{-γ/2}`
to the theorem's saving `n^{-δ_M}`. -/
theorem eq_14_to_16 {M : ℕ} (hM : 2 ≤ M) :
    ∃ C : ℝ, ∀ n p q : ℕ, 16 ≤ n → M ≤ R M n → p.Prime → p ∣ M →
      (R M n : ℝ) / M < (p ^ q : ℕ) → p ^ q ≤ R M n →
      let n' : ℝ := n
      let R' : ℝ := R M n
      let s' : ℝ := σ M n
      let D' : ℝ := (p ^ q : ℕ)
      let N' : ℝ := NN M n p q
      let g : ℝ := g₀ M
      let A' : ℝ := Acoef M
      -- the room and the legality of the call
      g * n' * √D' / s' ≤ N' ∧ n' ≤ g * n' * √D' / s' ∧
      D' ≤ R' ∧ R' ≤ n' ^ η M ∧ n' ^ η M ≤ N' ^ ((1 : ℝ) / 18) ∧
      D' ^ 18 ≤ N' ∧ D' ^ (1 + γ) ≤ N' ∧
      ((M : ℝ) ^ 2 + 1) * n' / s' ≤ (g' M n : ℝ) ∧
      (⌈A' * n' ^ 2 / s'⌉₊ : ℝ) ≤ (A' + 1) * n' ^ 2 / s' ∧
      -- (14)
      g ^ 2 * n' ^ 2 * √D' / s' ^ 2 ≤ N' ^ 2 / √D' ∧
      g ^ 2 / √(M : ℝ) * (n' ^ 2 / s') ≤ g ^ 2 * n' ^ 2 * √D' / s' ^ 2 ∧
      (A' + 1) * (n' ^ 2 / s') ≤ g ^ 2 / √(M : ℝ) * (n' ^ 2 / s') ∧
      -- the two bounds used for the cost
      ((p ^ ((q + 1) / 2) : ℕ) : ℝ) ≤ √(p * D') ∧
      (g' M n : ℝ) ≤ (g + 1) * n' / s' ∧
      -- (15)
      N' ^ 2 / D' ^ γ ≤ C * (n' ^ 2 * R' ^ (1 - γ) / s' ^ 2) ∧
      n' ^ 2 * R' ^ (1 - γ) / s' ^ 2 ≤ C * (n' ^ 2 * R' ^ (-γ / 2)) ∧
      -- the costs covered by (15)
      N' * D' ≤ C * (n' ^ 2 * R' ^ (-γ / 2)) ∧
      n' * √(p * D') ≤ C * (n' ^ 2 * R' ^ (-γ / 2)) ∧
      n' ^ 2 / s' ≤ C * (n' ^ 2 * R' ^ (-γ / 2)) ∧
      -- (16)
      s' ^ 2 * n' ^ 2 / R' + s' ≤ C * (n' ^ 2 * R' ^ (-γ / 2)) ∧
      -- the saving
      n' ^ 2 * R' ^ (-γ / 2) ≤ C * n' ^ (2 - δ M) := by sorry

end BddExp3SUM
