-- Prove2me | Theorems.Thm_FastMinority_lemma_3_6
-- name    : FastMinority.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:05.34453+00:00
-- url     : https://prove2.me/theorems/81b9f5d7-9342-4215-ab85-f48b8b133e4f
-- title:
--   Lemma 3.6 — the lower region is left into $\mathcal C\cup\mathcal H^+$ w.p. $\ge1-n^{-\gamma}$
-- statement:
--   Let $X$ be the minority-size chain of MINORITY with $n$ agents and odd sample size $k=\Theta(\log^2 n)$, let $D>2$, $L=\lceil n/(4k)\rceil$, $R=\lfloor n/2-n\sqrt{(2D\log n)/k}\rfloor$, $\mathcal L=[1,L-1]$, and let $\tau_{\mathcal L}=\inf\{t\ge0:X_t\notin\mathcal L\}$. For every fixed $\gamma>0$ and all sufficiently large $n$, uniformly over the initial states $x\in\mathcal L$,
--   $$
--   \Pr\big[\tau_{\mathcal L}<\infty,\ X_{\tau_{\mathcal L}}\in\{0\}\cup[L,R-1]\ \big|\ X_0=x\big]\ge1-n^{-\gamma};
--   $$
--   in fact this probability is already reached with $\tau_{\mathcal L}$ bounded by a finite horizon. Since $\{0\}\cup[L,R-1]\subseteq\mathcal C\cup\mathcal H^+$ for every value of $b$, this gives the source's $\Pr[\tau_{\mathcal L}<\infty,X_{\tau_{\mathcal L}}\in\mathcal C\cup\mathcal H^+\mid X_0=x]\ge1-n^{-\gamma}$.
--
--   A lower excursion never jumps to the upper region, w.h.p.
--
--   **Formalization Note** Here $k=\Theta(\log^2 n)$ is read as the band $a(\ln n)^2\le k\le A(\ln n)^2$ for arbitrary constants $0<a\le A$; all other constants are chosen after $a,A$ and before $n$, $k$ and the initial state. $D>2$ is arbitrary. The event with horizon $T$ is `hitWithin`.
--
--   Differences from the source:
--   - reading: k = Θ(log² n), for sufficiently large n → ∀ 0 < a ≤ A, then the statement's constants and N, then ∀ n ≥ N and every odd k with a(ln n)² ≤ k ≤ A(ln n)²; reason: Θ is a pair of band constants fixed first; constants depending on n or k would make the statement trivial
--   - reading: regions L = [1, L−1], C = [L, M′], H = [M′+1, R′−1], U = [R′, ⌊n/2⌋] for a constant D > 2, with M′ ≤ M and R′ ≥ R undefined → H = good set (3.1), U = [R, ⌊n/2⌋], C = [L, R−1] \ H, for every D > 2; reason: M′ and R′ are never defined; the page says it is enough to work with M and R
--   - generalization: X_{τ_L} ∈ C ∪ H⁺ → X_{τ_L} ∈ {0} ∪ [L, R − 1]; reason: {0} ∪ [L, R − 1] ⊆ C ∪ H⁺ for every b (proved in the sanity file), so the Lean event implies the printed one; b drops out
--   - generalization: τ_L < ∞ → ∃ a finite horizon T with Pr(τ_L ≤ T, X_{τ_L} ∈ target) ≥ 1 − n^{−γ}; reason: the probability with horizon T is at most the printed probability, so the Lean statement implies the printed one
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Lemma 3.6, p.10 (PDF p.12); proof p.21 (PDF p.23)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_FastMinority_lowerRegion
import Definitions.Def_FastMinority_escapeTarget
import Definitions.Def_FastMinority_hitWithin

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Lemma 3.6** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.10 = PDF p.12; proof p.21 = PDF p.23): with
`τ_𝓛 = inf{t ≥ 0 : X_t ∉ 𝓛}` the first exit time from the lower region, for every fixed `γ > 0` and
sufficiently large `n`, uniformly over all initial states `x ∈ 𝓛`,
`Pr[τ_𝓛 < ∞, X_{τ_𝓛} ∈ 𝓒 ∪ 𝓗⁺ | X₀ = x] ≥ 1 − n^{−γ}`.

**Formalization Note** `k = Θ(log² n)` is read as the band `a (ln n)² ≤ k ≤ A (ln n)²` for arbitrary constants `0 < a ≤ A`, chosen first; every other constant is chosen after them and before `n`, `k` and the initial state. The region constant `D > 2` is arbitrary. The exit target is the
`b`-free set `{0} ∪ [L, R − 1]` (`escapeTarget`), contained in `𝓒 ∪ 𝓗⁺` for every `b`. The event
`τ_𝓛 < ∞` is witnessed by a finite horizon `T`: `Pr_x(τ_𝓛 ≤ T, X_{τ_𝓛} ∈ target)` is `hitWithin`. -/
theorem lemma_3_6 :
    ∀ a A : ℝ, 0 < a → a ≤ A → ∀ D : ℝ, 2 < D → ∀ γ : ℝ, 0 < γ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, Odd k → a * Real.log n ^ 2 ≤ k → (k : ℝ) ≤ A * Real.log n ^ 2 →
      ∀ x ∈ lowerRegion n k, ∃ T : ℕ,
      1 - (n : ℝ) ^ (-γ) ≤ hitWithin (MinorityDynamics.actualKernel n k) (lowerRegion n k)ᶜ
          (escapeTarget n k D) T x := by sorry

end FastMinority
