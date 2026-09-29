-- Prove2me | Theorems.Thm_Devaney_exists_hasPrimePeriod_two
-- name    : Devaney.exists_hasPrimePeriod_two
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-17T14:22:33.611396+00:00
-- url     : https://prove2.me/theorems/f1719227-d187-4e0d-a4ec-416788f4aec0
-- title:
--   A period greater than two forces a period-two orbit
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be continuous. If $f$ has a periodic point whose least period $m$ satisfies $m>2$, then $f$ also has a periodic point of least period exactly $2$:
--
--   $$\exists\,x\ \text{of least period } m>2 \quad\Longrightarrow\quad \exists\,y \text{ of least period } 2.$$
--
--   This is the first and easiest step of Sharkovsky's theorem, corresponding to the fact that $2$ is the second-to-last entry of the Sharkovsky ordering: every period other than $1$ and $2$ lies before $2$. It is also the engine of the descent through the powers of two: applied to the iterate $f^{2^{a-1}}$ it converts a point of period $2^{m}$ into one of period $2^{a}$ for each $a<m$.
--
--   **Formalization Note** `HasPrimePeriod f x n` says that $n>0$, that $f^{n}(x)=x$, and that $f^{k}(x)\neq x$ for every $0<k<n$; that is, $n$ is the least period of $x$.
--
--   The source states the result for a continuous self-map of a compact interval; the statement here is for a continuous map of the whole real line, which is a weakening of the hypothesis. It remains valid because the argument only ever uses a covering relation $I\subseteq f(I)$, never the reverse inclusion $f(I)\subseteq I$.
-- source:
--   Bau-Sen Du, A Simple Proof of Sharkovsky's Theorem, arXiv:math/0606351v1 (2006), https://arxiv.org/abs/math/0606351, Section 2, Proposition 3 (proved there via Lemma 2).

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem exists_hasPrimePeriod_two (f : ℝ → ℝ) (hf : Continuous f) (m : ℕ) (hm : 2 < m)
    (h : ∃ x, HasPrimePeriod f x m) : ∃ y, HasPrimePeriod f y 2 := by sorry
end Devaney
