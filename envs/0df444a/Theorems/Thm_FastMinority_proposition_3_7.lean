-- Prove2me | Theorems.Thm_FastMinority_proposition_3_7
-- name    : FastMinority.proposition_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:57.201269+00:00
-- url     : https://prove2.me/theorems/cf03594c-33f8-420f-ba9f-db14423210a8
-- title:
--   Proposition 3.7 — weighted return bound $\max_{j\in\mathcal C}j\sum_{i\in\mathcal C}K(i,j)/i<3/4$
-- statement:
--   Let $X$ be the minority-size chain of MINORITY with $n$ agents and odd sample size $k=\Theta(\log^2 n)$, let $D>2$, and let $\mathcal R$ be the chain obtained by observing $X$ only at its successive visits to $\mathcal C\cup\mathcal H^+$ (stopped at $\mathcal H^+$), with transition matrix
--   $$
--   K(i,j)=P(i,j)+\sum_{\ell\ge2}P^\ell(i,j\mid\mathcal L\cup\mathcal U).
--   $$
--   There is a choice of the constant $b>0$ (in the definition of $\mathcal H$) such that for all sufficiently large $n$,
--   $$
--   \max_{j\in\mathcal C}\ j\cdot\sum_{i\in\mathcal C}\frac1i\,K(i,j)<\frac34 .
--   $$
--
--   With the weights $w_i=1/i$ and $\lambda=3/4$ this is condition (3.2) of Lemma 3.1 for $\mathcal R$ killed at $\mathcal H^+$, so $\mathcal R$ reaches $\mathcal H^+$ within $O(\log n)$ transitions w.h.p.
--
--   **Formalization Note** Here $k=\Theta(\log^2 n)$ is read as the band $a(\ln n)^2\le k\le A(\ln n)^2$ for arbitrary constants $0<a\le A$; all other constants are chosen after $a,A$ and before $n$, $k$ and the initial state. $D>2$ is arbitrary and $b$ is chosen after $a,A,D$. $K(i,j)$ is `returnKernel` with intermediate states outside $\mathcal C\cup\mathcal H^+$, in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: k = Θ(log² n), for sufficiently large n → ∀ 0 < a ≤ A, then the statement's constants and N, then ∀ n ≥ N and every odd k with a(ln n)² ≤ k ≤ A(ln n)²; reason: Θ is a pair of band constants fixed first; constants depending on n or k would make the statement trivial
--   - reading: regions L = [1, L−1], C = [L, M′], H = [M′+1, R′−1], U = [R′, ⌊n/2⌋] for a constant D > 2, with M′ ≤ M and R′ ≥ R undefined → H = good set (3.1), U = [R, ⌊n/2⌋], C = [L, R−1] \ H, for every D > 2; reason: M′ and R′ are never defined; the page says it is enough to work with M and R
--   - reading: K(i, j) = P(i, j) + Σ_{ℓ≥2} P^ℓ(i, j | L ∪ U), the kernel of R observed on C ∪ H⁺ → returnKernel with intermediate states outside C ∪ H⁺; reason: the definition of R ('observing … only at successive visits to C ∪ H⁺'); outside C ∪ H⁺ is L ∪ (U \ H), the page's L ∪ [R′, ⌊n/2⌋] with R′ the first state above the good states, since U = [R, ⌊n/2⌋] overlaps H for large n (R itself is good)
--   - encoding: max over j ∈ C of the weighted sum < 3/4 → the weighted sum < 3/4 for every j ∈ C, in ℝ≥0∞; reason: C is finite; a series of nonnegative terms in ℝ≥0∞
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Proposition 3.7, p.10 (PDF p.12); proof pp.22–35 (PDF pp.24–37)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_FastMinority_coreRegion
import Definitions.Def_FastMinority_goodPlus
import Definitions.Def_FastMinority_returnKernel

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Proposition 3.7** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.10 = PDF p.12; proof pp.22–35 = PDF pp.24–37): let `K(i, j)` be
the transition matrix of `𝓡`, the chain `X` observed at its successive visits to `𝓒 ∪ 𝓗⁺`. There is
a choice of the fixed constant `b` such that, for all sufficiently large `n`,
`max_{j ∈ 𝓒} j · ∑_{i ∈ 𝓒} (1/i) · K(i, j) < 3/4`.

**Formalization Note** `k = Θ(log² n)` is read as the band `a (ln n)² ≤ k ≤ A (ln n)²` for arbitrary constants `0 < a ≤ A`, chosen first; every other constant is chosen after them and before `n`, `k` and the initial state. The region constant `D > 2` is arbitrary and `b` is chosen after
`a, A, D`. `K(i, j) = returnKernel (actualKernel n k) (𝓒 ∪ 𝓗⁺) i j` (p.7: `K(i, j) = P(i, j) +
∑_{ℓ≥2} P^ℓ(i, j | 𝓛 ∪ 𝓤)`), with intermediate states outside `𝓒 ∪ 𝓗⁺`, in `ℝ≥0∞`. The maximum over
the finite set `𝓒` is below `3/4` iff every term is. -/
theorem proposition_3_7 :
    ∀ a A : ℝ, 0 < a → a ≤ A → ∀ D : ℝ, 2 < D →
      ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, Odd k → a * Real.log n ^ 2 ≤ k → (k : ℝ) ≤ A * Real.log n ^ 2 →
      ∀ j ∈ coreRegion n k D b,
      ((j : ℕ) : ENNReal) * ∑ i ∈ Finset.univ.filter (fun i => i ∈ coreRegion n k D b),
          (1 / ((i : ℕ) : ENNReal)) *
            returnKernel (MinorityDynamics.actualKernel n k) (coreRegion n k D b ∪ goodPlus n k b)
              i j < 3 / 4 := by sorry

end FastMinority
