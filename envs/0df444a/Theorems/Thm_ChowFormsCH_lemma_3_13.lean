-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_3_13
-- name    : ChowFormsCH.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:03.525451+00:00
-- url     : https://prove2.me/theorems/adef6400-30f2-4cdb-989f-36e4cfaeac46
-- title:
--   Lemma 3.13 — $\gcd(q,P')$ picks the factors of $q$ whose components of $V$ lie in $W$ (corrected: sign of $r_{j'}/q'$)
-- statement:
--   Let $K$ be algebraically closed, $V\subseteq K^{m+n}$ an $m$-equidimensional variety such that $y_1$ is a primitive element for $V$, $Q$ its general projection and $q,r_2,\dots,r_n\in K[x,y_1]$ its geometric resolution from eq. (1). Let $W\subseteq\mathbb P^{m+n}$ be an equidimensional projective variety of dimension $b$ with Chow form $C_W$ in $u_{0,0},\dots,u_{b,m+n}$. With new variables $w_{i,j}$ ($0\le i\le b$, $1\le j\le n+m$), $t_1,\dots,t_m$ and $s$, let
--   $$
--   g_i:=\sum_{j=1}^m w_{i,j}(x_j-t_jz)+w_{i,m+1}(y_1-sz)+\sum_{j'=2}^n w_{i,m+j'}\Big(y_{j'}-\frac{r_{j'}(t,s)}{q'(t,s)}z\Big),\qquad i=0,\dots,b .
--   $$
--   Let $P(t,s,w)/q'(t,s)^c=C_W(\mathrm{coeff}(g_0),\dots,\mathrm{coeff}(g_b))$ with $P\in K[t,s,w]$ relatively prime to $q'$, and let $P'\in K[t,s]$ be the GCD of the coefficients of $P$ as a polynomial in $w$. Then $\gcd(q(t,s),P'(t,s))$ consists of those irreducible factors of $q$ that correspond to components of $V$ lying in $W$: an irreducible factor $p$ of $q$ divides it if and only if every component of $V$ over $p=0$ lies in (the affine part of) $W$.
--
--   This is the pruning step of Theorem 4.9: it removes from $V^\star_k$ the components lying on higher-dimensional pieces.
--
--   **Formalization Note** $K[t,s]$ is $K[t_1,\dots,t_m][s]$, the ring of $q,r_j,q'$; the coefficients of $g_i$ live in its fraction field and the exponent $c$ is an integer. Coordinates of $\mathbb P^{m+n}$ are ordered $(z,x,y)$. Since $q$ is squarefree (Lemma 3.8), the condition on irreducible factors determines the gcd up to a unit.
--
--   Differences from the source:
--   - correction: g_i contains y_{j′} + (r_{j′}(t,s)/q′(t,s)) z → y_{j′} − (r_{j′}(t,s)/q′(t,s)) z; reason: on V, q′y_j − r_j vanishes (Definition 3.3, Lemma 3.9), so y_j = r_j/q′. Counterexample to the printed sign: K = ℚ̄, m = 1, n = 2, V = {(x, 0, 1)}, Q = T − u₂, q = y₁, r₂ = 1, q′ = 1, W the closure of V with C_W = (u₀₀ + u₀₃)u₁₁ − u₀₁(u₁₀ + u₁₃); the printed g_i give C_W(coeff g) = −w₀₂w₁₁s + 2w₀₃w₁₁ + w₀₁w₁₂s − 2w₀₁w₁₃, so P′ = 1 and gcd(q, P′) = 1 although V ⊆ W; the corrected sign gives s(w₀₁w₁₂ − w₀₂w₁₁) and gcd = s = q
--   - encoding: gcd(q, P′) consists of those factors of q that correspond to components of V that lie in W → every gcd g of q and P′ satisfies: an irreducible factor p of q divides g iff every irreducible component Z of V with q-image on p = 0 is contained in the affine part of W; reason: the paper's bijection between irreducible factors of q and components of V (p.26); q squarefree makes this determine g up to a unit
--   - reading: q, r₂, …, rₙ a geometric resolution for V as above → q, r_j defined from the general projection Q by eq. (1); reason: "as above" refers to the resolution constructed in §3.2
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 3.13, pp.27–28 (PDF pp.29–30)

import Mathlib
import Definitions.Def_ChowFormsCH_comps
import Definitions.Def_ChowFormsCH_IsChowForm
import Definitions.Def_ChowFormsCH_affTrace
import Definitions.Def_ChowFormsCH_IsPrimitiveY1
import Definitions.Def_ChowFormsCH_IsGeneralProjection
import Definitions.Def_ChowFormsCH_IsSqfPart

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 3.13** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, pp.27–28), corrected: sign of
`r_{j′}/q′`. Let `V ⊂ K^{m+n}` be an `m`-equidimensional variety with primitive element `y₁`, and
`q, r₂, …, rₙ ∈ K[x, y₁]` its geometric resolution from eq. (1). Let `W ⊂ P^{m+n}` be an
equidimensional variety of dimension `b` with Chow form `C_W` in `u_{0,0}, …, u_{b,m+n}`. For
`i = 0, …, b` let
`g_i := Σ_{j=1}^m w_{i,j}(x_j − t_j z) + w_{i,m+1}(y₁ − s z) + Σ_{j′=2}^n w_{i,m+j′}(y_{j′} − (r_{j′}(t,s)/q′(t,s)) z)`.
Let `P(t, s, w)/q′(t, s)^c = C_W(coeff(g₀), …, coeff(g_b))` with `P ∈ K[t, s, w]` relatively prime to
`q′`, and `P′ ∈ K[t, s]` the GCD of the coefficients of `P` as a polynomial in `w`. Then
`gcd(q(t, s), P′(t, s))` consists of those factors of `q` that correspond to components of `V` that
lie in `W`.

**Formalization Note** `K` is algebraically closed. The ring `K[t, s]` is `K[t₁, …, t_m][s]`, the ring
of `q`, `r_j`, `q′` (`x ↦ t`, `y₁ ↦ s`); the coefficients of `g_i` live in its fraction field. The
coordinates of `P^{m+n}` are ordered `(z, x, y)` (`zxyCoord`); `w_{i,j}` is `X (i, inl (j−1))` for
`j ≤ m` and `w_{i,m+j′}` is `X (i, inr (j′−1))`. An irreducible factor `p` of `q` corresponds to the
component `Z` of `V` whose projection to `(x, y₁)` lies on `p = 0` (p.26: "the irreducible components
of V are in bijection with the irreducible factors of the polynomial q"); since `q` is squarefree
(Lemma 3.8), the conclusion determines the gcd up to a unit: an irreducible factor `p` of `q` divides
it iff every component of `V` lying over `p = 0` is contained in the affine part of `W`. The
printed `y_{j′} + (r_{j′}/q′) z` is corrected to `y_{j′} − (r_{j′}/q′) z`. -/
theorem lemma_3_13 {K : Type} [Field K] [IsAlgClosed K] {m n b : ℕ} [NeZero n]
    (V : Set (AffSp (Fin m ⊕ Fin n) K)) (hV : IsPrimitiveY1 V)
    (Q : Polynomial (MvPolynomial (Fin n ⊕ Fin m) K)) (hQ : IsGeneralProjection V Q)
    (W : Set (ProjSpace (m + n) K)) (hW : IsProjVariety W) (hWeq : IsProjEquidim W b)
    (CW : MvPolynomial (Fin (b + 1) × Fin (m + n + 1)) K) (hCW : IsNormalizedChowForm W b CW)
    (P : MvPolynomial (Fin (b + 1) × (Fin m ⊕ Fin n)) (Polynomial (MvPolynomial (Fin m) K)))
    (c : ℤ)
    (hP : MvPolynomial.map (algebraMap (Polynomial (MvPolynomial (Fin m) K))
            (FractionRing (Polynomial (MvPolynomial (Fin m) K)))) P
          = MvPolynomial.C ((algebraMap (Polynomial (MvPolynomial (Fin m) K))
              (FractionRing (Polynomial (MvPolynomial (Fin m) K)))
              (Polynomial.derivative (resQ Q))) ^ c) *
            MvPolynomial.aeval (fun ij : Fin (b + 1) × Fin (m + n + 1) =>
              (zxyCoord ij.2).elim
                (-(∑ l : Fin m, MvPolynomial.X (ij.1, Sum.inl l) *
                      MvPolynomial.C (algebraMap (Polynomial (MvPolynomial (Fin m) K))
                        (FractionRing (Polynomial (MvPolynomial (Fin m) K)))
                        (Polynomial.C (MvPolynomial.X l)))
                    + MvPolynomial.X (ij.1, Sum.inr 0) *
                      MvPolynomial.C (algebraMap (Polynomial (MvPolynomial (Fin m) K))
                        (FractionRing (Polynomial (MvPolynomial (Fin m) K))) Polynomial.X)
                    + ∑ l ∈ Finset.univ.filter (fun l : Fin n => l ≠ 0),
                      MvPolynomial.X (ij.1, Sum.inr l) *
                        MvPolynomial.C (algebraMap (Polynomial (MvPolynomial (Fin m) K))
                            (FractionRing (Polynomial (MvPolynomial (Fin m) K))) (resR Q l) /
                          algebraMap (Polynomial (MvPolynomial (Fin m) K))
                            (FractionRing (Polynomial (MvPolynomial (Fin m) K)))
                            (Polynomial.derivative (resQ Q)))))
                (fun v => MvPolynomial.X (ij.1, v))) CW)
    (hPcop : IsRelPrime P (MvPolynomial.C (Polynomial.derivative (resQ Q))))
    (P' : Polynomial (MvPolynomial (Fin m) K))
    (hP' : IsGcdOfSet (Set.range fun μ => P.coeff μ) P')
    (g : Polynomial (MvPolynomial (Fin m) K)) (hg : IsGcdOf (resQ Q) P' g) :
    ∀ p : Polynomial (MvPolynomial (Fin m) K), Irreducible p → p ∣ resQ Q →
      (p ∣ g ↔ ∀ Z ∈ comps V, (∀ v ∈ Z, evalXY1 p v = 0) → Z ⊆ affTrace W) := by sorry

end ChowFormsCH
