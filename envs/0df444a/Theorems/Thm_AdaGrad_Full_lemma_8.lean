-- Prove2me | Theorems.Thm_AdaGrad_Full_lemma_8
-- name    : AdaGrad.Full.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:45:31.571221+00:00
-- url     : https://prove2.me/theorems/25045ab8-98a9-4e9f-b596-5afd48f3687f
-- title:
--   Lemma 8 — $2\operatorname{tr}((B-\nu gg^\top)^{1/2})\le2\operatorname{tr}(B^{1/2})-\nu\operatorname{tr}(B^{-1/2}gg^\top)$
-- statement:
--   Let $B$ be a real symmetric positive semidefinite $d\times d$ matrix, and let $B^{-1/2}$ denote the square root of the inverse of $B$ when $B\succ0$ and the square root of the pseudo-inverse $B^\dagger$ otherwise. Let $g\in\mathbb R^d$ and $\nu\ge0$ be such that $B-\nu gg^\top\succeq0$. Then
--   $$2\operatorname{tr}\big((B-\nu gg^\top)^{1/2}\big)\le2\operatorname{tr}(B^{1/2})-\nu\operatorname{tr}\big(B^{-1/2}gg^\top\big).$$
--
--   This is a first-order concavity inequality for $\operatorname{tr}(A^{1/2})$ that remains valid at singular $B$; with $B=G_T$, $\nu=1$, $g=g_T$ it drives the induction of Lemma 10.
--
--   **Formalization Note** The hypothesis $\nu\ge0$ is added: the page says "for any $\nu$", but the statement is false for $\nu<0$ (take $B=0$, $\nu=-1$, $g\ne0$: it would give $2\|g\|_2\le0$); the paper's proof uses $\nu>0$ and applies the lemma with $\nu=1$. $B^{-1/2}$ is written as $(B^\dagger)^{1/2}$, which covers both cases of the definition.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2134, Lemma 8 (proof pp. 2150–2151)

import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2
open scoped MatrixOrder InnerProductSpace

namespace AdaGrad.Full

/-- Lemma 8 (p. 2134), with `ν ≥ 0`: if `B ⪰ 0` and `B − ν g g⊤ ⪰ 0` then
`2 tr((B − ν g g⊤)^{1/2}) ≤ 2 tr(B^{1/2}) − ν tr(B^{−1/2} g g⊤)`, where `B^{−1/2} = (B†)^{1/2}`
is the root of the (pseudo-)inverse of `B`. -/
theorem lemma_8 {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef)
    (g : EuclideanSpace ℝ (Fin d)) (ν : ℝ) (hν : 0 ≤ ν) (h : (B - ν • outer g).PosSemidef) :
    2 * (CFC.sqrt (B - ν • outer g)).trace
      ≤ 2 * (CFC.sqrt B).trace - ν * (CFC.sqrt (pinv B) * outer g).trace := by sorry

end AdaGrad.Full
