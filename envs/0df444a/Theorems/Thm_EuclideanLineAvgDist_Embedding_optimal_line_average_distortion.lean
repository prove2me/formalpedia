-- Prove2me | Theorems.Thm_EuclideanLineAvgDist_Embedding_optimal_line_average_distortion
-- name    : EuclideanLineAvgDist.Embedding.optimal_line_average_distortion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:11.890199+00:00
-- url     : https://prove2.me/theorems/b09eaa03-94a0-4715-a025-b8918d0a212a
-- title:
--   Theorem 1.1 — every n-point Euclidean metric embeds non-expansively into the line with average distortion $O(\sqrt{\log n/\log\log n})$
-- statement:
--   There is a universal constant $C>0$ with the following property. For an integer $k\ge1$, let $X\subset\mathbb R^k$ be a set of $n$ points in Euclidean space. Then there exists a non-expansive embedding into the line $f:X\to\mathbb R$, that is $|f(x)-f(y)|\le\|x-y\|_2$ for all $x,y\in X$, such that
--   $$\sum_{x,y\in X}\|x-y\|_2\;\le\;C\sqrt{\frac{\log n}{\log\log n}}\;\sum_{x,y\in X}|f(x)-f(y)|\qquad(n\ge3),$$
--   and, for every $n$, the same inequality with $\log n/\log\log n$ replaced by $\rho(n)=\log\max(3,n)/\log\log\max(3,n)$. Equivalently, $\operatorname{avd}(f)\le C\sqrt{\log n/\log\log n}$ for $n\ge3$.
--
--   This is the source's statement $\operatorname{avd}(f)\in O\bigl(\sqrt{\log n/\log\log n}\bigr)$, which matches the lower bound of Matoušek–Rabinovich and improves the previous $O(\sqrt{\log n})$. The constant does not depend on $n$, $k$ or $X$. The paper's proof gives $C=\max(256,\,64\cdot8192\sqrt{4(3+2\log2)})$.
--
--   **Formalization Note** $X$ is a finite set of points of `EuclideanSpace ℝ (Fin k)`, a space with the Euclidean norm, and $f$ is defined on $X$. Sums run over ordered pairs. The ratio is never formed: for $n\ge2$ the inequality forces $\sum|f(x)-f(y)|>0$, and for $n\le1$ both sides vanish.
--
--   Differences from the source:
--   - encoding: $\operatorname{avd}(f)\in O(\cdot)$ → $\exists C>0$ placed before $k$ and $X$; reason: the meaning of $O$ with a constant independent of $n$, $k$ and $X$
--   - generalization: rate $\sqrt{\log n/\log\log n}$, undefined for $n\le2$ → $\sqrt{\rho(n)}$ with $n$ replaced by $\max(3,n)$, so the bound is claimed for every $n$; reason: equal for $n\ge3$, which is the source's claim; for $n\le1$ both sides vanish and for $n=2$ the map $x\mapsto\|x-x_1\|_2$ has distortion $1$
--   - encoding: $\operatorname{avd}(f)\le C\sqrt{\cdot}$ → $S_d\le C\sqrt{\cdot}\,S_f$; reason: avoids the ratio; for $n\ge2$ the inequality forces $S_f>0$ and is equivalent to the ratio bound
-- source:
--   Jack Spalding-Jamieson, STOC 2027 submission #1643 (October 2026), p. 2, Theorem 1.1 (proof pp. 6–7)

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic

open scoped BigOperators
set_option autoImplicit false

namespace EuclideanLineAvgDist.Embedding

/-- Theorem 1.1 (p. 2). There is a universal constant `C > 0` such that for every integer `k ≥ 1`
and every set `X ⊂ ℝᵏ` of `n` points there is a non-expansive `f : X → ℝ` (with respect to the
Euclidean distance) with `avd(f) ≤ C · √(log n / log log n)`, stated cross-multiplied as
`∑_{x,y ∈ X} ‖x - y‖₂ ≤ C · √(log n / log log n) · ∑_{x,y ∈ X} |f(x) - f(y)|`
(with `n` replaced by `max 3 n` inside the rate). -/
theorem optimal_line_average_distortion :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ X : Finset (Eucl k),
      ∃ f : X → ℝ, NonExpansive f ∧
        distSum X ≤ C * Real.sqrt (logRate X.card) * lineSpread f := by sorry

end EuclideanLineAvgDist.Embedding
