-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_3_10
-- name    : ChowFormsCH.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:40.277196+00:00
-- url     : https://prove2.me/theorems/646644fe-6f39-4eed-9880-454927a8c83e
-- title:
--   Lemma 3.10 — $q$ defines the projection of $V$ onto $(x,y_1)$: $\pi_{x,y_1}(V)=V(q)$
-- statement:
--   Let $K$ be algebraically closed and $V\subseteq K^{m+n}$ an equidimensional variety of dimension $m$ such that $y_1$ is a primitive element for $V$, with general projection $Q$ and $q:=Q(\nu_0,x,y_1)$. Then $q$ defines the projection of $V$ onto the first $m+1$ coordinates:
--   $$
--   \pi_{x,y_1}(V)=V(q)=\{(\alpha,\beta_1)\in K^{m}\times K : q(\alpha,\beta_1)=0\}.
--   $$
--
--   This is the first condition of Definition 3.3, and it makes the irreducible factors of $q$ correspond to the components of $V$.
--
--   **Formalization Note** The projection itself, not its closure, is compared with $V(q)$.
--
--   Differences from the source:
--   - encoding: the standing assumption of §3.2 and Q as constructed in Lemmas 3.5–3.6 → hypotheses IsPrimitiveY1 V and IsGeneralProjection V Q; reason: the section's standing assumption written as binders; Q characterized over K determines the same polynomial
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 3.10, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_ChowFormsCH_IsPrimitiveY1
import Definitions.Def_ChowFormsCH_IsGeneralProjection

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 3.10** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.26). For an equidimensional
variety `V ⊂ K^{m+n}` of dimension `m` such that `y₁` is a primitive element for `V`, with `Q` the
general projection and `q := Q(ν₀, x, y₁)` (eq. (1)): `q` defines the projection of `V` onto the
first `m + 1` coordinates, `π_{x,y₁}(V) = V(q)`.

**Formalization Note** `K` is algebraically closed. The projection `π_{x,y₁}(V)` itself (not its
closure) is compared with the zero set of `q` in `K^m × K`. -/
theorem lemma_3_10 {K : Type} [Field K] [IsAlgClosed K] {m n : ℕ} [NeZero n]
    (V : Set (AffSp (Fin m ⊕ Fin n) K)) (hV : IsPrimitiveY1 V)
    (Q : Polynomial (MvPolynomial (Fin n ⊕ Fin m) K)) (hQ : IsGeneralProjection V Q) :
    {p : (Fin m → K) × K | ∃ v ∈ V, (∀ j : Fin m, (show Fin m ⊕ Fin n → K from v) (Sum.inl j) = p.1 j) ∧
        (show Fin m ⊕ Fin n → K from v) (Sum.inr 0) = p.2}
      = {p : (Fin m → K) × K | Polynomial.eval p.2 ((resQ Q).map (MvPolynomial.eval p.1)) = 0} := by sorry

end ChowFormsCH
