-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_lemma_C_1
-- name    : CorrelatedLocalSearch.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:32.24556+00:00
-- url     : https://prove2.me/theorems/b6c18145-ba74-4b5e-88d3-09c3e9b1ab6f
-- title:
--   Lemma C.1 (integer-potential barrier), (20)
-- statement:
--   Fix integers $k/2<r<k$ and $\lambda,s_*$ as in (8). Consider a deterministic process driven by symbols in $[k]$, with stopping time $\tau$, satisfying the integer-potential hypotheses: initial potential $h\ge1$, every live history has potential $d\ge1$, at least $r$ of the $k$ next symbols terminate or give potential at most $d-1$, and every other symbol terminates or gives potential at most $d+1$. Then for every integer $m>h$, every $T\ge0$, every $D\ge1$ and every $\nu\in\mathcal Q_{s_*,D}$,
--   $$
--   \mathbb P_\nu\{\tau>T\}\ \le\ \min\Bigl\{1,\ D\Bigl[\frac hm\lambda^{h-m}+\frac{\lambda^h}{\sqrt{\lambda^2-1}}\exp\Bigl(-\frac{\pi^2T}{2(2m-1)^2}\Bigr)\Bigr]\Bigr\}.
--   $$
--
--   Nothing here is specific to SAT: the potential plays the role of a Lyapunov function whose drift condition is replaced by a worst-case count of favourable symbols, and the bound holds for every source in the class, Markov or not.
--
--   **Formalization Note** $\nu\{\tau>T\}$ is the outer measure of the set (which is a finite union of cylinders). $\lambda^{h-m}$ is an integer power.
--
--   Differences from the source:
--   - encoding: integers k/2 < r < k → natural numbers k, r with k < 2r and r < k; reason: same instances
--   - encoding: a deterministic process with live histories, a potential and a stopping time τ → a liveness predicate `live` and a potential `pot` on words; a history is live in the paper's sense when all its prefixes satisfy `live` (`Surv`); τ = hitTime live ∈ ℕ∞, ⊤ if it never stops; reason: every deterministic process driven by the tape is described this way, and conversely
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, Lemma C.1, eq. (20), p.21 (PDF p.23)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_SourceClass
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_IsPotentialProcess

set_option autoImplicit false

namespace CorrelatedLocalSearch

open MeasureTheory

/-- Lemma C.1 (integer-potential barrier), (20) (Xu, *Local Search with Correlated
Randomness*, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, Lemma C.1, eq. (20), p.21): fix
`k/2 < r < k` and `λ, s∗` of (8). For a deterministic process driven by symbols in `[k]`
satisfying the potential hypotheses (`IsPotentialProcess`) with initial potential `h ≥ 1`, for
every integer `m > h`, every `T ≥ 0`, every `D ≥ 1` and every `ν ∈ Q_{s∗,D}`,
`P_ν{τ > T} ≤ min{1, D[(h/m) λ^{h−m} + λ^h/√(λ²−1) · exp(−π²T/(2(2m−1)²))]}`.

**Formalization Note** The process is given by its live histories and potential; `τ` is
`hitTime live`, valued in `ℕ∞`. `ν {τ > T}` is the outer measure of the set (the set is a
finite union of cylinders, hence measurable). `λ^{h−m}` is an integer power. -/
theorem lemma_C_1 (k r : ℕ) (hk : k < 2 * r) (hr : r < k)
    (live : List (Fin k) → Prop) (pot : List (Fin k) → ℕ) (h : ℕ)
    (hP : IsPotentialProcess k r live pot h) (m : ℕ) (hm : h < m) (T : ℕ) (D : ℝ) (hD : 1 ≤ D)
    (ν : Measure (ℕ → Fin k)) (hν : ν ∈ SourceClass k (sStar k r) D) :
    ν {ω | (T : ℕ∞) < hitTime live ω} ≤
      ENNReal.ofReal (min 1 (D * ((h : ℝ) / m * lam k r ^ ((h : ℤ) - m) +
        lam k r ^ h / Real.sqrt (lam k r ^ 2 - 1) *
          Real.exp (-(Real.pi ^ 2 * T) / (2 * (2 * (m : ℝ) - 1) ^ 2))))) := by sorry

end CorrelatedLocalSearch
