-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_5_12
-- name    : CNFLearnMQ.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:36.419642+00:00
-- url     : https://prove2.me/theorems/38593666-9882-431d-8f8d-573176163c2d
-- title:
--   Lemma 5.12 — at most $\Xi(t)$ strong edges on every path of the extension forest
-- statement:
--   Let $t\ge1$ be real, $k\ge100$ and $d\ge1$ integers satisfying the local lemma condition (3), $k\ge(1+1/t)\log d+2\log k+t-3\log t+5$, and let $\Phi=(V,C)$ be an $n$-variable $(k,d)$-CNF formula with $n\ge k$ (the standing assumptions of §5, p.21, and §3, p.13).
--   Every path in the extension forest $\mathcal T$ contains at most $\Xi(t)$ strong edges.
--
--   A path starts at a seed $s_0$ of width $\lceil k/(t+1)\rceil$; its $j$-th edge $s_j\to s_j\cup b_j$ adds a signed core $b_j=(B_j,\tau_j)$ with $B_j\cap S_j=\emptyset$, $|B_j|\ge1$ and $|S_j|+|B_j|\le k$. With $r=k-|S_j|$ and $h=|B_j|$ the edge is **strong** if $1/(r\binom rh)\le d\rho$ and weak otherwise (Definition 5.9). The statement is made for every sequence of widths $w_0=\lceil k/(t+1)\rceil$, $w_{j+1}=w_j+h_j$ with $h_j\ge1$ and $w_j+h_j\le k$: at most $\Xi(t)$ indices $j$ are strong.
--
--   This bounds the exponent of $n$ in the size of the extension forest.
--
--   Differences from the source:
--   - generalization: paths of the extension forest $\mathcal T$ of a run → every width sequence starting at $\lceil k/(t+1)\rceil$ with steps $h_j\ge1$ and $w_j+h_j\le k$; reason: strongness depends only on $|S_j|$ and $|B_j|$, and every path of $\mathcal T$ yields such a sequence
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 5.12, p.29 (Definitions 5.9, 5.10, p.28)

import Mathlib
import Definitions.Def_CNFLearnMQ_Ntot

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 5.12, p.29 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Under the standing assumptions of §5 (`t ≥ 1`, `k ≥ 100`, `d ≥ 1`, (3)),
every path in the extension forest `T` contains at most `Ξ(t)` strong edges.

A path of `T` (Definition 5.10, p.28) starts at a seed `s_0` of width `⌈k/(t + 1)⌉`, and its `j`-th
edge `s_j → s_{j+1} = s_j ∪ b_j` adds a signed core `b_j = (B_j, τ_j)` with `B_j ∩ S_j = ∅`,
`|B_j| ≥ 1` and `|S_j| + |B_j| ≤ k`. By Definition 5.9 (p.28) the edge is strong iff
`1/(r·binom(r, h)) ≤ dρ` with `r = k − |S_j|` and `h = |B_j|`. Strongness depends only on the widths
`w_j = |S_j|` and `h_j = |B_j|`, so the statement is made for every width sequence of this form.

**Formalization Note** Every root-to-node path of `T` produces such a width sequence; the statement
is for all such sequences. -/
theorem lemma_5_12 {k d : ℕ} {t : ℝ} (ht : 1 ≤ t) (hk : 100 ≤ k) (hd : 1 ≤ d)
    (hLLL : LLLCondition k d t) (ℓ : ℕ) (w hb : ℕ → ℕ) (h0 : w 0 = seedSize k t)
    (hstep : ∀ j < ℓ, w (j + 1) = w j + hb j) (hpos : ∀ j < ℓ, 1 ≤ hb j)
    (hle : ∀ j < ℓ, w j + hb j ≤ k) :
    ((Finset.range ℓ).filter fun j =>
      ((((k - w j) * (k - w j).choose (hb j) : ℕ) : ℝ))⁻¹ ≤ (d : ℝ) * rho k d).card ≤ Xi t := by sorry

end CNFLearnMQ
