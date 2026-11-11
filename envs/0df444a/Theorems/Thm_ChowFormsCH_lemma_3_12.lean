-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_3_12
-- name    : ChowFormsCH.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:45.621028+00:00
-- url     : https://prove2.me/theorems/a646f2cb-0b51-49a8-b7e8-461dc9dd76d9
-- title:
--   Lemma 3.12 — the general projection $Q(u,w,T)$ is a specialization of the Chow form of $\overline V$
-- statement:
--   Let $K$ be algebraically closed and $V\subseteq K^{m+n}$ an equidimensional variety of dimension $m$ such that $y_1$ is a primitive element for $V$. Let $\overline V\subseteq\mathbb P^{m+n}$ be its projective closure, homogenized with a new variable $z$, and $C_{\overline V}$ its Chow form. Let $\ell_i=w_iz-x_i$ for $i=1,\dots,m$ and $\ell_{m+1}=Tz-\sum_{j=1}^n u_jy_j$. Then
--   $$
--   C_{\overline V}\big(\mathrm{coeff}(\ell_1),\dots,\mathrm{coeff}(\ell_{m+1})\big)=Q(u,w,T),
--   $$
--   where $Q$ defines the general projection of $V$.
--
--   Together with Lemmas 3.8–3.11 this computes a geometric resolution of $V$ from a Chow form, the second step of Theorem 4.9.
--
--   **Formalization Note** The coordinates of $\mathbb P^{m+n}$ are ordered $(z,x_1,\dots,x_m,y_1,\dots,y_n)$; the $i$-th group of Chow-form variables ($i=0,\dots,m$) receives the coefficient vector of $\ell_{i+1}$. $Q(u,w,T)$ is $Q$ with its $x$-variables renamed $w$.
--
--   Differences from the source:
--   - reading: ℓ_{m+1} = Tz − Σ_{j=1}^n u_i y_i → ℓ_{m+1} = Tz − Σ_{j=1}^n u_j y_j; reason: the summation index is j; the printed u_i y_i is a typo
--   - encoding: Q constructed over the algebraic closure of K(u) as Q₁⋯Q_t (Lemmas 3.5–3.6) → Q characterized over K: monic in T, and f vanishes on {(μ, α, Σ μ_j β_j)} iff Q ∣ f; reason: this determines the same polynomial (see IsGeneralProjection)
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 3.12, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_ChowFormsCH_IsChowForm
import Definitions.Def_ChowFormsCH_affTrace
import Definitions.Def_ChowFormsCH_IsPrimitiveY1
import Definitions.Def_ChowFormsCH_IsGeneralProjection

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 3.12** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.27). Let `V ⊂ K^{m+n}` be an
equidimensional variety such that `y₁` is a primitive element for `V`, `V̄ ⊂ P^{m+n}` its projective
closure (homogenizing variable `z`) and `C_V̄` its Chow form. Let `ℓ_i = w_i z − x_i` for
`i = 1, …, m` and `ℓ_{m+1} = Tz − Σ_{j=1}^n u_j y_j`. Then
`C_V̄(coeff(ℓ₁), …, coeff(ℓ_{m+1})) = Q(u, w, T)`, where `Q` defines the general projection of `V`.

**Formalization Note** `K` is algebraically closed; `V` has dimension `m` (Definition 3.2). The
coordinates of `P^{m+n}` are ordered `(z, x₁, …, x_m, y₁, …, yₙ)` (`zxyCoord`); the group `i` of
variables of `C_V̄` (`i = 0, …, m`) receives the coefficient vector of `ℓ_{i+1}`. The variables
`w₁, …, w_m` are the `x`-variables of the ring `K[u, x][T]` of `Q` (`Q(u, w, T)` is `Q` with
`x := w`). The source's `Σ_j u_i y_j` is read as `Σ_j u_j y_j`. -/
theorem lemma_3_12 {K : Type} [Field K] [IsAlgClosed K] {m n : ℕ} [NeZero n]
    (V : Set (AffSp (Fin m ⊕ Fin n) K)) (hV : IsPrimitiveY1 V)
    (C : MvPolynomial (Fin (m + 1) × Fin (m + n + 1)) K)
    (hC : IsNormalizedChowForm (projClosure V) m C)
    (Q : Polynomial (MvPolynomial (Fin n ⊕ Fin m) K)) (hQ : IsGeneralProjection V Q) :
    MvPolynomial.aeval (fun ij : Fin (m + 1) × Fin (m + n + 1) =>
        if h : ij.1.val < m then
          (zxyCoord ij.2).elim
            (Polynomial.C (MvPolynomial.X (Sum.inr ⟨ij.1.val, h⟩)) :
              Polynomial (MvPolynomial (Fin n ⊕ Fin m) K))
            (Sum.elim (fun j : Fin m => if j.val = ij.1.val then -1 else 0) (fun _ : Fin n => 0))
        else
          (zxyCoord ij.2).elim (Polynomial.X : Polynomial (MvPolynomial (Fin n ⊕ Fin m) K))
            (Sum.elim (fun _ : Fin m => 0)
              (fun j : Fin n => (-Polynomial.C (MvPolynomial.X (R := K) (σ := Fin n ⊕ Fin m) (Sum.inl j)) :
                Polynomial (MvPolynomial (Fin n ⊕ Fin m) K))))) C = Q := by sorry

end ChowFormsCH
