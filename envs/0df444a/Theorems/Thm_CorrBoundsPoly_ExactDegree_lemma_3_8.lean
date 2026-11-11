-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_lemma_3_8
-- name    : CorrBoundsPoly.ExactDegree.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:53.452611+00:00
-- url     : https://prove2.me/theorems/f81b935f-1324-4df9-84ec-d3f074c6d6d7
-- title:
--   Lemma 3.8 — reflection identity $\eta(m,D)=\mathbb P(\tau_D>m)$ and the doubling recurrence
-- statement:
--   Let $S_t$ be a simple symmetric random walk on $\mathbb Z$ starting at $0$, and $\tau_D=\inf\{t\ge0:|S_t|=D\}$.
--   1. For every integer $D\ge1$ and $m\ge0$,
--   $$\eta(m,D)=\mathbb P(\tau_D>m). \tag{3.11}$$
--   2. When $D$ is dyadic, this satisfies the binomial recurrence
--   $$\eta(m,2D)=\mathbb E_{K\sim\mathrm{Bin}(\lfloor m/2\rfloor,1/2)}\,\eta(K,D),\qquad \eta(m,1)=\mathbf 1\{m=0\}. \tag{3.12}$$
--
--   Together with Lemma 3.5 this identifies the rank defect $a_D(m)$ of the dyadic elementary cores with $\eta(m,D)$ (Corollary 3.9).
--
--   Differences from the source:
--   - encoding: $\mathbb P(\tau_D>m)$ → $2^{-m}$ times the number of step sequences $\varepsilon\in\{\pm1\}^m$ with $|S_t|\ne D$ for all $t\le m$ (`survival D m`); reason: the event depends only on the first $m$ steps, which are uniform on $\{\pm1\}^m$
--   - encoding: $\mathbb E_{K\sim\mathrm{Bin}(r,1/2)}$ → the finite sum `binomExp`; reason: definition of the binomial law
--   - encoding: the inner sum over $j\ge0$ in $\eta$ → $0\le j\le m$; reason: the other terms vanish for $D\ge1$
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 29 (PDF 31), Lemma 3.8, Eqs. (3.11), (3.12)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_ElemSym
import Definitions.Def_CorrBoundsPoly_ExactDegree_RandomWalk

namespace CorrBoundsPoly.ExactDegree

/-- **Lemma 3.8** (Reflection identity and survival; Xin Li, *More on Correlation Bounds for
Polynomials*, p. 29, PDF 31). Let `S_t` be the simple symmetric random walk on `ℤ` from `0` and
`τ_D = inf{t ≥ 0 : |S_t| = D}`. (1) For every integer `D ≥ 1` and `m ≥ 0`, `η(m, D) = P(τ_D > m)`
(Eq. (3.11)). (2) For dyadic `D`, `η(m, 2D) = E_{K∼Bin(⌊m/2⌋,1/2)} η(K, D)`, and
`η(m, 1) = 1{m=0}` (Eq. (3.12)). -/
theorem lemma_3_8 :
    (∀ D m : ℕ, 1 ≤ D → eta m D = survival D m) ∧
    (∀ D : ℕ, IsDyadic D → ∀ m : ℕ, eta m (2 * D) = binomExp (m / 2) (fun k => eta k D)) ∧
    (∀ m : ℕ, eta m 1 = if m = 0 then 1 else 0) := by sorry

end CorrBoundsPoly.ExactDegree
