-- Prove2me | Theorems.Thm_FastMinority_lemma_3_4
-- name    : FastMinority.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:06:17.225193+00:00
-- url     : https://prove2.me/theorems/896f4ff7-ad28-4ed5-8d04-fed99323f9ed
-- title:
--   Lemma 3.4 — the upper region is left within $C_\gamma\log n/\log k$ rounds w.p. $\ge1-n^{-\gamma}$
-- statement:
--   Let $X$ be the minority-size chain of MINORITY with $n$ agents and odd sample size $k=\Theta(\log^2 n)$, let $D>2$, $R=\lfloor n/2-n\sqrt{(2D\log n)/k}\rfloor$, $\mathcal U=[R,\lfloor n/2\rfloor]$, and let $\tau_{\mathcal U}=\inf\{t\ge0:X_t<R\}$ be the first exit time from $\mathcal U$. For every fixed $\gamma>0$ there is a constant $C_\gamma>0$ such that, for all sufficiently large $n$,
--   $$
--   \sup_{x\in\mathcal U}\Pr\Big[\tau_{\mathcal U}>C_\gamma\,\frac{\log n}{\log k}\ \Big|\ X_0=x\Big]\le n^{-\gamma}.
--   $$
--
--   Near the balanced configuration the fluctuations of one round create an imbalance that later rounds amplify, so the chain leaves $\mathcal U$ in $O(\log n/\log k)$ rounds.
--
--   **Formalization Note** Here $k=\Theta(\log^2 n)$ is read as the band $a(\ln n)^2\le k\le A(\ln n)^2$ for arbitrary constants $0<a\le A$; all other constants are chosen after $a,A$ and before $n$, $k$ and the initial state. $D>2$ is arbitrary and chosen with $a,A$; $C_\gamma$ depends on $a,A,D,\gamma$.
--
--   Differences from the source:
--   - reading: k = Θ(log² n), for sufficiently large n → ∀ 0 < a ≤ A, then the statement's constants and N, then ∀ n ≥ N and every odd k with a(ln n)² ≤ k ≤ A(ln n)²; reason: Θ is a pair of band constants fixed first; constants depending on n or k would make the statement trivial
--   - reading: regions L = [1, L−1], C = [L, M′], H = [M′+1, R′−1], U = [R′, ⌊n/2⌋] for a constant D > 2, with M′ ≤ M and R′ ≥ R undefined → H = good set (3.1), U = [R, ⌊n/2⌋], C = [L, R−1] \ H, for every D > 2; reason: M′ and R′ are never defined; the page says it is enough to work with M and R
--   - encoding: Pr[τ_U > C_γ log n/log k] → Pr(τ_U > ⌊C_γ log n/log k⌋); reason: τ_U is an integer
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Lemma 3.4, p.9 (PDF p.11); proof pp.16–19 (PDF pp.18–21)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_FastMinority_upperRegion

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Lemma 3.4** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.9 = PDF p.11; proof pp.16–19 = PDF pp.18–21): with
`τ_U = inf{t ≥ 0 : X_t < R}` the first exit time from `𝓤`, for every fixed `γ > 0` there is a
constant `C_γ > 0` such that, for sufficiently large `n`,
`sup_{x ∈ 𝓤} Pr[τ_U > C_γ · log n / log k | X₀ = x] ≤ n^{−γ}`.

**Formalization Note** `k = Θ(log² n)` is read as the band `a (ln n)² ≤ k ≤ A (ln n)²` for arbitrary constants `0 < a ≤ A`, chosen first; every other constant is chosen after them and before `n`, `k` and the initial state. The region constant `D > 2` is arbitrary (chosen with `a, A`);
`𝓤 = [R, ⌊n/2⌋]` (`R′ := R`, see `upperRegion`). `Pr(τ_U > u)` is `avoidProb … ⌊u⌋₊ x`. -/
theorem lemma_3_4 :
    ∀ a A : ℝ, 0 < a → a ≤ A → ∀ D : ℝ, 2 < D → ∀ γ : ℝ, 0 < γ →
      ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, Odd k → a * Real.log n ^ 2 ≤ k → (k : ℝ) ≤ A * Real.log n ^ 2 →
      ∀ x ∈ upperRegion n k D,
      MinorityDynamics.avoidProb (MinorityDynamics.actualKernel n k)
          {s | (s : ℕ) < upThr n k D} ⌊Cγ * Real.log n / Real.log k⌋₊ x ≤ (n : ℝ) ^ (-γ) := by sorry

end FastMinority
