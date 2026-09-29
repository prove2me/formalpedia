-- Prove2me | Theorems.Thm_FoundationsML_DimReduction_johnson_lindenstrauss
-- name    : FoundationsML.DimReduction.johnson_lindenstrauss
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:29:54.140724+00:00
-- url     : https://prove2.me/theorems/392eb5e1-209b-44ba-a46b-06078de93e07
-- title:
--   Lemma 15.4 — Johnson-Lindenstrauss lemma (goal)
-- statement:
--   **Statement (Lemma 15.4, Johnson-Lindenstrauss, p. 355, PDF p. 372).** For any
--   $0<\epsilon<1/2$ and any integer $m>4$, let $k=20\log(m)/\epsilon^2$. Then for any set $V$
--   of $m$ points in $\mathbb R^N$, there exists a map $f:\mathbb R^N\to\mathbb R^k$ such that
--   for all $u,v\in V$,
--   $$(1-\epsilon)\|u-v\|^2 \le \|f(u)-f(v)\|^2 \le (1+\epsilon)\|u-v\|^2.$$
--
--   This is the chapter's second headline result: any finite set of points in an arbitrarily
--   high-dimensional space can be embedded into a space of dimension only $O(\log m/\epsilon^2)$
--   — independent of the ambient dimension $N$ — while distorting every pairwise squared
--   distance by at most a factor of $(1\pm\epsilon)$. The proof is a textbook example of the
--   probabilistic method: Lemma 15.3 gives each of the $O(m^2)$ pairs a strictly-positive
--   success probability for a *fixed* random Gaussian map, and a union bound shows the
--   probability that *all* pairs succeed simultaneously is still strictly positive, so some map
--   achieving the guarantee must exist.
--
--   **Formalization Note.** The book's $k=20\log(m)/\epsilon^2$ is a real number in general;
--   since a map's target dimension must be a natural number, $k$ is taken here to be
--   $\lceil 20\log(m)/\epsilon^2\rceil$ (`Nat.ceil`), which only strengthens the book's own
--   success-probability argument (a larger $k$ only decreases each pair's failure probability
--   in the union bound), so the existential conclusion is no weaker than the book's own. The
--   statement is a bare existential ("there exists a map $f$"), matching the book's own
--   printed form exactly — not a universally-quantified claim about a specific random
--   construction succeeding with a stated probability, which is what Lemma 15.3 (not this
--   lemma) states.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 355, Lemma 15.4 (PDF p. 372)

import Mathlib
import Definitions.Def_FoundationsML_DimReduction_SqNorm

namespace FoundationsML.DimReduction

/-- Lemma 15.4 (Johnson-Lindenstrauss; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 355, PDF p. 372 — this mission's goal). For any
`0 < ε < 1/2` and any integer `m > 4`, let `k = ⌈20 log(m)/ε²⌉`. Then for any set `V` of `m`
points in `ℝ^N`, there exists a map `f : ℝ^N → ℝ^k` such that for all `u, v ∈ V`,
`(1−ε)‖u−v‖² ≤ ‖f(u)−f(v)‖² ≤ (1+ε)‖u−v‖²`.

**Formalization Note.** The book's `k = 20 log(m)/ε²` is a real number in general; since the
target dimension of a map into `ℝ^k` must be a natural number, `k` is taken to be
`⌈20 log(m)/ε²⌉` (`Nat.ceil`), which only strengthens the book's own success-probability
argument (rounding up the number of dimensions can only decrease the failure probability of
each pair in the union bound the book's proof uses), so the existential conclusion is no
weaker than the book's. The statement is a bare existential, matching the book's own "there
exists a map `f`" exactly — not a universally-quantified probabilistic claim about a specific
random construction, which is what Lemma 15.3 (not this lemma) states. -/
theorem johnson_lindenstrauss {N : ℕ} (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (m : ℕ) (hm : 4 < m) (V : Finset (Fin N → ℝ)) (hV : V.card = m) :
    ∃ f : (Fin N → ℝ) → (Fin ⌈20 * Real.log (m : ℝ) / ε ^ 2⌉₊ → ℝ),
      ∀ u ∈ V, ∀ v ∈ V,
        (1 - ε) * SqNorm (u - v) ≤ SqNorm (f u - f v) ∧
          SqNorm (f u - f v) ≤ (1 + ε) * SqNorm (u - v) := by sorry

end FoundationsML.DimReduction
