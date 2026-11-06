-- Prove2me | Theorems.Thm_FastMinority_proposition_3_3
-- name    : FastMinority.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:06:15.037439+00:00
-- url     : https://prove2.me/theorems/cae2e820-646b-4f53-98ee-6e3fce802ac4
-- title:
--   Proposition 3.3 — the cost of reaching $\mathcal C\cup\mathcal H^+$ is $\le C\log n/\log k$ w.p. $\ge1-n^{-\gamma}$
-- statement:
--   Let $X$ be the minority-size chain of MINORITY with $n$ agents and odd sample size $k=\Theta(\log^2 n)$, let $D>2$, and for a state $i$ let $c(i)$ be the cost of transitioning from $i$ to the next state in $\mathcal C\cup\mathcal H^+$: one plus the number of steps outside $\mathcal C\cup\mathcal H^+$, i.e. $c(i)=\inf\{t\ge1:X_t\in\mathcal C\cup\mathcal H^+\}$ for $X_0=i$. For every $\gamma>0$ there is a constant $C=C(\gamma)>0$ such that for all sufficiently large $n$ and every state $i$,
--   $$
--   \Pr\Big[c(i)\le C\,\frac{\log n}{\log k}\Big]\ge1-n^{-\gamma},
--   $$
--   and this holds even with $\mathcal C\cup\mathcal H^+$ replaced by its subset $\{0\}\cup[L,R-1]$.
--
--   Each transition of the induced chain $\mathcal R$ costs $O(\log n/\log k)$ rounds of $X$, w.h.p.
--
--   **Formalization Note** Here $k=\Theta(\log^2 n)$ is read as the band $a(\ln n)^2\le k\le A(\ln n)^2$ for arbitrary constants $0<a\le A$; all other constants are chosen after $a,A$ and before $n$, $k$ and the initial state. $D>2$ is arbitrary; $C$ depends on $a,A,D,\gamma$. The event $c(i)>u$ is "$X_t\notin$ target for $1\le t\le\lfloor u\rfloor$", written with `stayProb`.
--
--   Differences from the source:
--   - reading: k = Θ(log² n), for sufficiently large n → ∀ 0 < a ≤ A, then the statement's constants and N, then ∀ n ≥ N and every odd k with a(ln n)² ≤ k ≤ A(ln n)²; reason: Θ is a pair of band constants fixed first; constants depending on n or k would make the statement trivial
--   - reading: regions L = [1, L−1], C = [L, M′], H = [M′+1, R′−1], U = [R′, ⌊n/2⌋] for a constant D > 2, with M′ ≤ M and R′ ≥ R undefined → H = good set (3.1), U = [R, ⌊n/2⌋], C = [L, R−1] \ H, for every D > 2; reason: M′ and R′ are never defined; the page says it is enough to work with M and R
--   - generalization: next state in C ∪ H⁺ → next state in {0} ∪ [L, R − 1]; reason: a subset of C ∪ H⁺ for every b, so c(i) for the subset bounds the printed c(i); b drops out
--   - generalization: i ∈ [n/2] → every i with 2i ≤ n, including i = 0; reason: i = 0 is immediate (0 is absorbing and in the target); specializes
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Proposition 3.3, p.9 (PDF p.11); proof p.10 (PDF p.12)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_FastMinority_escapeTarget

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Proposition 3.3** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.9 = PDF p.11; proof p.10 = PDF p.12): for any state `i` let
`c(i)` be the cost of transitioning from `i` to the next state in `𝓒 ∪ 𝓗⁺` (one plus the number of
steps outside `𝓒 ∪ 𝓗⁺`, p.7), i.e. `c(i) = inf{t ≥ 1 : X_t ∈ 𝓒 ∪ 𝓗⁺}` from `X₀ = i`. Then, for a
suitable constant `C = C(γ) > 0`, `Pr[c(i) ≤ C · log n / log k] ≥ 1 − n^{−γ}`.

**Formalization Note** `k = Θ(log² n)` is read as the band `a (ln n)² ≤ k ≤ A (ln n)²` for arbitrary constants `0 < a ≤ A`, chosen first; every other constant is chosen after them and before `n`, `k` and the initial state. The region constant `D > 2` is arbitrary. The target is the `b`-free
set `{0} ∪ [L, R − 1]` (`escapeTarget`) ⊆ `𝓒 ∪ 𝓗⁺`. `Pr(c(i) > u)` is the probability of
`X_t ∉ target` for `1 ≤ t ≤ ⌊u⌋₊`: `stayProb` with no constraint at time `0`. -/
theorem proposition_3_3 :
    ∀ a A : ℝ, 0 < a → a ≤ A → ∀ D : ℝ, 2 < D → ∀ γ : ℝ, 0 < γ →
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, Odd k → a * Real.log n ^ 2 ≤ k → (k : ℝ) ≤ A * Real.log n ^ 2 →
      ∀ i : Fin (n + 1), 2 * (i : ℕ) ≤ n →
      MinorityDynamics.stayProb (MinorityDynamics.actualKernel n k)
          (fun t => if t = 0 then Set.univ else (escapeTarget n k D)ᶜ)
          ⌊C * Real.log n / Real.log k⌋₊ i ≤ (n : ℝ) ^ (-γ) := by sorry

end FastMinority
