-- Prove2me | Theorems.Thm_ConservativeVCSP_Treewidth_lemma_4_7
-- name    : ConservativeVCSP.Treewidth.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:47:51.938541+00:00
-- url     : https://prove2.me/theorems/fb091ea0-75ac-4d03-ab26-d3997c1ff8f4
-- title:
--   Lemma 4.7 — unary costs, a reversing move and a restriction on a pair give all costs on the pair
-- statement:
--   Let $D$ be a finite domain, $\Gamma$ a constraint language over $D$ and $P=\{p,q\}\subseteq D$ with $p\ne q$. Suppose $\Gamma$ expresses all finite-valued unary cost functions on $P$, a finite-valued reversing move on $P$ (a finite-valued $g\in\mathrm{pow}(\Gamma)$ with $g(p,q)=g(q,p)<g(p,p)=g(q,q)$) and a restriction to $P$. Then for every $r\ge1$ and every $f:P^r\to\mathbb Q_{\ge0}$ there are a finite-valued $g\in\mathrm{pow}(\Gamma)$ and $c\in\mathbb Q$ with
--   $$g(\bar x)=f(\bar x)+c\qquad(\bar x\in P^r).$$
--
--   It is the two-element base case of the expressibility results (Lemma 4.8, Corollary 6.13).
--
--   Differences from the source:
--   - encoding: cost values in $\mathbb{Q}_{\ge 0}\cup\{\infty\}$, additive shifts $c\in\mathbb{Q}$ → `WithTop ℚ≥0`; a shift is applied after the inclusion `toQ` into `WithTop ℚ` (with ∞ + c = ∞); reason: Lean convention; the same functions and the same shifts
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), p. 22, Lemma 4.7

import Definitions.Def_ConservativeVCSP_Treewidth_Moves

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

/-- Lemma 4.7 (Costs on a two-element set, p. 22): if `Γ` expresses all finite-valued unary cost
functions on `P = {p, q}` (`p ≠ q`), a finite-valued reversing move on `P` and a restriction to
`P`, then `Γ` expresses all finite-valued cost functions on `P`. -/
theorem lemma_4_7 {D : Type} [Fintype D] [Nonempty D] (Γ : Set (CostFn D)) (hΓ : IsLanguage Γ)
    (p q : D) (hpq : p ≠ q)
    (hunary : ExpressesAllUnaryFV Γ {p, q})
    (hrev : FVMove Γ p q q p)
    (hres : ExpressesRestriction Γ {p, q}) :
    ExpressesAllFV Γ {p, q} := by sorry

end ConservativeVCSP.Treewidth
