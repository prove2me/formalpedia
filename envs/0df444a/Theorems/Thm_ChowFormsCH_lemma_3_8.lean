-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_3_8
-- name    : ChowFormsCH.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:52.042696+00:00
-- url     : https://prove2.me/theorems/0a8516eb-97ef-4dfd-8c03-1d0588a8111e
-- title:
--   Lemma 3.8 — the discriminant of $q=Q(\nu_0,x,y_1)$ is nonzero; $q$ has no multiple factor
-- statement:
--   Let $K$ be algebraically closed and $V\subseteq K^{m+n}$ an equidimensional variety of dimension $m$ such that $y_1$ is a primitive element for $V$. Let $Q$ define the general projection of $V$ and $q:=Q(\nu_0,x,y_1)\in K[x][y_1]$ with $\nu_0=(1,0,\dots,0)$ (eq. (1)). Then the discriminant $\delta\in K[x]$ of $q$ with respect to $y_1$ is nonzero; equivalently, $q$ has no multiple factor:
--   $$
--   \delta\neq 0\qquad\text{and}\qquad q \text{ is squarefree}.
--   $$
--
--   This is the second condition of Definition 3.3 (geometric resolution) for $q,r_2,\dots,r_n$.
--
--   **Formalization Note** $\delta$ is Mathlib's `Polynomial.discr` of $q$ over $K[x]$; both sides of "equivalently" are stated.
--
--   Differences from the source:
--   - encoding: the standing assumption of §3.2 ("fix an equidimensional variety V of dimension m such that y1 is a primitive element for V") and Q as constructed in Lemmas 3.5–3.6 → hypotheses IsPrimitiveY1 V and IsGeneralProjection V Q; reason: the section's standing assumption written as binders; Q characterized over K determines the same polynomial
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 3.8, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_ChowFormsCH_IsPrimitiveY1
import Definitions.Def_ChowFormsCH_IsGeneralProjection

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 3.8** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.25). For an equidimensional
variety `V ⊂ K^{m+n}` of dimension `m` such that `y₁` is a primitive element for `V`, with `Q` the
general projection and `q := Q(ν₀, x, y₁)` (eq. (1)): the discriminant `δ` of `q` with respect to
`y₁` is nonzero; equivalently, `q` has no multiple factor.

**Formalization Note** `K` is algebraically closed; `q ∈ K[x][y₁]` (`resQ Q`), `δ` is Mathlib's
`Polynomial.discr` in `K[x]`; both halves of the "equivalently" are stated, "no multiple factor" as
`Squarefree q`. -/
theorem lemma_3_8 {K : Type} [Field K] [IsAlgClosed K] {m n : ℕ} [NeZero n]
    (V : Set (AffSp (Fin m ⊕ Fin n) K)) (hV : IsPrimitiveY1 V)
    (Q : Polynomial (MvPolynomial (Fin n ⊕ Fin m) K)) (hQ : IsGeneralProjection V Q) :
    Polynomial.discr (resQ Q) ≠ 0 ∧ Squarefree (resQ Q) := by sorry

end ChowFormsCH
