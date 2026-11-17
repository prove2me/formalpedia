-- Prove2me | Theorems.Thm_AGProxGap_Supplement_theorem_4_8
-- name    : AGProxGap.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:20:23.925872+00:00
-- url     : https://prove2.me/theorems/4112d6fa-1e19-4324-93ef-56befac36852
-- title:
--   Theorem 4.8 — the resultant step: agreement on $I_{\nu,H}$, at most $B_{\nu,H}$ agreements off it, $\sum B_{\nu,H}\le4mD_YD_Z+\ell D_Y$
-- statement:
--   Work in the setting of §4: a one-point AG code $C=C_L(D,mP_\infty)$ on a curve $X/\mathbb F_q$ with $m\ge2\mathfrak g-1$, $\ell\ge1$, words $u_0,\dots,u_\ell$ and $r_i(Z)=\sum_ju_{j,i}Z^j$. Fix the following data (every choice is allowed):
--   1. a nonzero $Q(Y,Z)\in\mathbb F_q(X)[Y,Z]$ with $\deg_YQ\le D_Y$ and $\deg_ZQ\le D_Z$, a set $S\subseteq\mathbb F_q$ and functions $f_z\in L(G)$, $z\in S$;
--   2. a factorization $Q=C(Z)\prod_{\nu=1}^rH_\nu(Y,Z)^{e_\nu}$ in $\overline{\mathbb F}_q(X)[Y,Z]$ with $C\ne0$, the $H_\nu$ irreducible, pairwise nonassociate, of positive $Y$-degree, and $e_\nu\ge1$;
--   3. $\mu_\nu=p^{a_\nu}$ ($p=\operatorname{char}\mathbb F_q$), $a_\nu$ maximal with $H_\nu(Y,Z)=R_\nu(Y^{\mu_\nu},Z)$;
--   4. a point $P_0\in X(\overline{\mathbb F}_q)\setminus\{P_\infty,P_1,\dots,P_n\}$ at which all coefficients of every $R_\nu$ are regular, with $\deg_YR_{\nu,P_0}=\deg_YR_\nu$, $\deg_Y\partial_YR_{\nu,P_0}=\deg_Y\partial_YR_\nu$ and $\operatorname{Res}_Y(R_{\nu,P_0},\partial_YR_{\nu,P_0})\neq0$, and a local parameter $t$ at $P_0$;
--   5. $S'\subseteq S$, the parameters with $C(z)\ne0$, $\mathrm{lc}_Y(R_{\nu,P_0})(z)\ne0$ and $\operatorname{Res}_Y(R_{\nu,P_0},\partial_YR_{\nu,P_0})(z)\ne0$ for all $\nu$; each $z\in S'$ is assigned to the first $\nu$ with $R_\nu(f_z^{\mu_\nu},z)=0$, and $y_z=f_z(P_0)^{\mu_\nu}$;
--   6. for each $\nu$, coefficients $\lambda_{i,j}\in\overline{\mathbb F}_q$ with $h(P_i)=\sum_{j=0}^{\mu_\nu m}\lambda_{i,j}[t^j]h$ for all $h\in L_{\overline{\mathbb F}_q}(\mu_\nu mP_\infty)$, and the $F_i$ of (9);
--   7. $\mathcal H_\nu$, the set of factors of a fixed irreducible factorization of the $Y$-primitive part of $R_{\nu,P_0}$ in $\overline{\mathbb F}_q[Y,Z]$, and $S_{\nu,H}=\{z\in S':z\text{ assigned to }\nu,\ H(y_z,z)=0\}$.
--
--   For $H\in\mathcal H_\nu$ let $I_{\nu,H}=\{i\in[n]:H\mid F_i\text{ in }\overline{\mathbb F}_q[Y,Z]\}$ and
--   $$B_{\nu,H}=(\deg_YH)\bigl(2\mu_\nu m\deg_ZR_\nu+\ell\mu_\nu\bigr)+(\deg_ZH)\bigl(2\mu_\nu m\deg_YR_\nu\bigr).$$
--   Then for every $\nu$ and $H\in\mathcal H_\nu$:
--   1. if $i\in I_{\nu,H}$, then $f_z(P_i)=r_i(z)$ for every $z\in S_{\nu,H}$;
--   2. if $i\notin I_{\nu,H}$, then $|\{z\in S_{\nu,H}:f_z(P_i)=r_i(z)\}|\le B_{\nu,H}$;
--
--   and moreover
--   $$\sum_{\nu=1}^r\sum_{H\in\mathcal H_\nu}B_{\nu,H}\le4mD_YD_Z+\ell D_Y.$$
--
--   This is the step of the proof of Theorem 4.1 that converts the interpolation polynomial into coordinatewise agreement information: coordinates in $I_{\nu,H}$ agree on the whole class $S_{\nu,H}$, and the others agree only boundedly often.
--
--   **Formalization Note** Bivariate polynomials have outer variable $Y$ and inner variable $Z$; $\operatorname{Res}_Y$ is Mathlib's resultant, the $Y$-primitive part is Mathlib's primitive part over $\overline{\mathbb F}_q[Z]$, and $H(Y,Z)=R(Y^\mu,Z)$ is polynomial expansion. "$H\mid F_i$" is $F_i=HG$ in $\overline{\mathbb F}_q(Y,Z)$ for a polynomial $G$, since $F_i$ is formed as a rational function. The algebraic closure and the points on $X_{\overline{\mathbb F}_q}$ are the datum `ClosureExt`.
--
--   Differences from the source:
--   - generalization: Q a nonzero polynomial of the form (4) satisfying the interpolation conditions (5) (Lemma 4.4), with §4's D_Y, D_Z → any nonzero Q ∈ F[Z][Y] with deg_Y Q ≤ DY and deg_Z Q ≤ DZ, for any naturals DY, DZ; reason: the proof of Theorem 4.8 uses only these degree bounds (through (6)); the paper's Q satisfies them by (4)
--   - generalization: S the set of Theorem 4.1 with fixed MCA-bad witnesses (z, f_z, A_z) → any S ⊆ F_q and any f_z ∈ L(G) for z ∈ S; reason: the proof uses only f_z ∈ L(G) and the definitions of S′, the assignment and S_{ν,H}; the paper's S and f_z are a special case
--   - encoding: F̄_q, F̄_q(X), the points P_i, P_∞ on X_{F̄_q} → a ClosureExt datum (algebraic closure K, function field FK = K·F, the unique places above P_i, P_∞); reason: over the perfect field F_q this is the paper's base change
--   - encoding: polynomials in F̄_q(X)[Y, Z] and F̄_q[Y, Z]; deg_Y, deg_Z, ∂_Y, Res_Y, lc_Y, Y-primitive part → Polynomial (Polynomial _) with outer Y; natDegree, degZ, derivative, Polynomial.resultant, leadingCoeff, primPart; reason: Lean convention; resultant vanishing is independent of the sign convention of the Sylvester matrix
--   - encoding: F_i ∈ F̄_q[Y, Z] defined by (9); H | F_i in F̄_q[Y, Z] → F_i formed in the fraction field F̄_q(Y, Z); H | F_i as F_i = H·G for a polynomial G; reason: (9) is a rational expression and Lemma 4.7 proves it is a polynomial; for a polynomial F_i the two divisibility notions coincide
--   - encoding: ℋ_ν, the irreducible factors of a fixed factorization; ν ∈ {1, …, r}, 'the first ν' → the elements of a multiset of irreducibles whose product is associate to the primitive part; ν : Fin r with its order; reason: Lean convention; same objects
--   - encoding: a smooth projective geometrically irreducible curve X/F_q of genus 𝔤, points of X(F_q), C = C_L(D, mP_∞) → a field F with IsCurveOver F_q F, Algebra.EssFiniteType F_q F, ConstantsAreBase F_q F; rational places (IsRational) in OnePointData; genus genusFF F_q F; reason: the base mission's convention; over a finite (perfect) field these are exactly the function fields of such curves
--   - encoding: §4's assumption m ≥ 2𝔤 − 1 → 2 * genusFF F_q F ≤ m + 1 in ℕ; reason: same condition without natural subtraction
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §4.2, Theorem 4.8, p.31; construction pp.25–31 ((6), Lemma 4.5, (7), (8), (9), Lemma 4.2 on p.23)

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AGProxGap_OnePointData
import Definitions.Def_AGProxGap_divG
import Definitions.Def_AGProxGap_rpoly
import Definitions.Def_AGProxGap_Supplement_ClosureExt
import Definitions.Def_AGProxGap_Supplement_localCoeff
import Definitions.Def_AGProxGap_Supplement_specAt
import Definitions.Def_AGProxGap_Supplement_liftSeq
import Definitions.Def_AGProxGap_Supplement_Fpoly

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial
open Classical

universe u v

namespace AGProxGap.Supplement

/-- **Theorem 4.8** (the resultant step of §4.2; (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §4.2, p.31): "For each ν ∈ {1, . . . , r},
let F_i be the polynomials constructed in (9) for this ν. For every H ∈ ℋ_ν, define
I_{ν,H} := {i ∈ [n] : H | F_i in F̄_q[Y, Z]} and
B_{ν,H} := (deg_Y H)(2μ_ν m deg_Z R_ν + ℓμ_ν) + (deg_Z H)(2μ_ν m deg_Y R_ν).
Theorem 4.8. With the notation above, for every ν ∈ {1, . . . , r} and H ∈ ℋ_ν, the following
hold: (i) If i ∈ I_{ν,H}, then f_z(P_i) = r_i(z) for every z ∈ S_{ν,H}. (ii) If i ∉ I_{ν,H},
then |{z ∈ S_{ν,H} : f_z(P_i) = r_i(z)}| ≤ B_{ν,H}. Moreover,
Σ_{ν=1}^r Σ_{H∈ℋ_ν} B_{ν,H} ≤ 4mD_Y D_Z + ℓD_Y."

"The notation above" (pp.23–31) is the following, every choice universally quantified:
1. the code: `F/F_q` a function field with full constant field, `OnePointData P Pinf m`, §4's
   `m ≥ 2𝔤 − 1`, `ℓ ≥ 1`, words `u_0, …, u_ℓ`, `r_i(Z)` the base `rpoly`;
2. `Q ∈ F_q(X)[Y, Z]` nonzero with `deg_Y Q ≤ D_Y`, `deg_Z Q ≤ D_Z`; a set `S ⊆ F_q` and
   `f_z ∈ L(G)` for `z ∈ S`;
3. the algebraic closure datum `E` (`F̄_q`, `F̄_q(X)`, the points `P_i`, `P_∞` on `X_{F̄_q}`);
4. a factorization `Q = C(Z) ∏_{ν=1}^r H_ν^{e_ν}` in `F̄_q(X)[Y, Z]` with `C ≠ 0` in `F̄_q(X)[Z]`,
   the `H_ν` irreducible, pairwise nonassociate, of positive `Y`-degree, `e_ν ≥ 1`;
5. `μ_ν = p^{a_ν}` (`p = char F_q`) with `a_ν` maximal such that `H_ν(Y, Z) = R_ν(Y^{μ_ν}, Z)`;
6. a point `P_0 ∈ X(F̄_q) ∖ {P_∞, P_1, …, P_n}` with the properties of Lemma 4.5: all coefficients
   of every `R_ν` regular at `P_0`, `deg_Y R_{ν,P_0} = deg_Y R_ν`,
   `deg_Y ∂_Y R_{ν,P_0} = deg_Y ∂_Y R_ν`, `Res_Y(R_{ν,P_0}, ∂_Y R_{ν,P_0}) ≠ 0`; a local parameter `t`
   at `P_0`;
7. `S'`: the `z ∈ S` with `C(z) ≠ 0`, `lc_Y(R_{ν,P_0})(z) ≠ 0` and
   `Res_Y(R_{ν,P_0}, ∂_Y R_{ν,P_0})(z) ≠ 0` for every `ν`; `z ∈ S'` is assigned to the first `ν`
   with `R_ν(f_z^{μ_ν}, z) = 0`; `y_z = f_z(P_0)^{μ_ν}`;
8. coefficients `λ_{i,0}, …, λ_{i,μ_ν m} ∈ F̄_q` with `h(P_i) = Σ_j λ_{i,j}[t^j]h` for every
   `h ∈ L_{F̄_q}(μ_ν m P_∞)` (Lemma 4.2), and `F_i` as in (9) (`Fpoly`, with `α_{ν,j}` of (7));
9. `ℋ_ν`: the factors of a fixed irreducible factorization of the `Y`-primitive part of
   `R_{ν,P_0}` in `F̄_q[Y, Z]`; `S_{ν,H} = {z ∈ S' assigned to ν : H(y_z, z) = 0}`.

**Formalization Note** Bivariate polynomials are `Polynomial (Polynomial _)` (outer `Y`, inner
`Z`); `deg_Y` is `natDegree`, `deg_Z` is `degZ`, `∂_Y` is `derivative`, `Res_Y` is Mathlib's
`resultant` (Sylvester determinant at the natural degrees), `lc_Y` is `leadingCoeff`, the
`Y`-primitive part is `primPart` over `F̄_q[Z]`. `H_ν = R_ν(Y^{μ_ν}, Z)` is `expand`. The
factorization in item 9 is a multiset of irreducibles whose product is associate to the primitive
part; `ℋ_ν` is its set of elements. `f_z(P_0)`, `f_z(P_i)` use `Place.evalAt` (of the image of
`f_z` in `F̄_q(X)` at `P_0`; of `f_z` itself at `P_i` over `F_q`). Indices `ν` run over `Fin r`,
"first" is the order of `Fin r`. `H | F_i in F̄_q[Y, Z]` is `F_i = H·G` in `F̄_q(Y, Z)` for a
polynomial `G`. The statement is more general than the paper's in three places, each of which
the paper's data satisfy: `Q` need only be nonzero with `deg_Y Q ≤ D_Y`, `deg_Z Q ≤ D_Z` (the
paper's `Q` satisfies (4), (5); (5) is not used), `S` is any set of parameters and `f_z` any
function in `L(G)` (the paper's `S` is Theorem 4.1's set with MCA-bad witnesses `f_z`), and
`D_Y, D_Z` are any bounds for those degrees (the paper's are §4's). -/
theorem theorem_4_8 (Fq : Type u) [Field Fq] [Fintype Fq] (F : Type v) [Field F] [Algebra Fq F]
    [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F] (hconst : ConstantsAreBase Fq F)
    (n m : ℕ) (P : Fin n → Place Fq F) (Pinf : Place Fq F) (hD : AGProxGap.OnePointData P Pinf m)
    (hgenus : 2 * genusFF Fq F ≤ m + 1) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (u : Fin (ℓ + 1) → Fin n → Fq)
    -- the interpolation polynomial, the parameters and the decoded functions
    (DY DZ : ℕ) (Q : Polynomial (Polynomial F)) (hQ : Q ≠ 0) (hQY : Q.natDegree ≤ DY)
    (hQZ : degZ Q ≤ DZ) (S : Finset Fq) (f : Fq → F)
    (hf : ∀ z ∈ S, f z ∈ LSpace (AGProxGap.divG Pinf m))
    -- the base change to the algebraic closure
    (E : ClosureExt P Pinf)
    -- the factorization of Q over the algebraic closure
    (r : ℕ) (Cz : Polynomial E.FK) (hCz : Cz ≠ 0) (H : Fin r → Polynomial (Polynomial E.FK))
    (ex : Fin r → ℕ) (hHirr : ∀ ν, Irreducible (H ν)) (hHdeg : ∀ ν, 0 < (H ν).natDegree)
    (hHna : ∀ ν ν', ν ≠ ν' → ¬ Associated (H ν) (H ν')) (hex : ∀ ν, 1 ≤ ex ν)
    (hfac : Q.map (Polynomial.mapRingHom (algebraMap F E.FK)) = C Cz * ∏ ν, H ν ^ ex ν)
    -- removing the inseparable part
    (a : Fin r → ℕ) (R : Fin r → Polynomial (Polynomial E.FK))
    (hR : ∀ ν, H ν = expand (Polynomial E.FK) (ringChar Fq ^ a ν) (R ν))
    (hamax : ∀ ν (b : ℕ) (R' : Polynomial (Polynomial E.FK)),
      H ν = expand (Polynomial E.FK) (ringChar Fq ^ b) R' → b ≤ a ν)
    -- the auxiliary point P₀ of Lemma 4.5 and a local parameter t at P₀
    (P0 : Place E.K E.FK) (hP0inf : P0 ≠ E.liftInf) (hP0 : ∀ i, P0 ≠ E.lift i)
    (hreg : ∀ ν k l, ((R ν).coeff k).coeff l ∈ P0.toValuationSubring)
    (hdegY : ∀ ν, (specAt P0 (R ν)).natDegree = (R ν).natDegree)
    (hdegD : ∀ ν, (derivative (specAt P0 (R ν))).natDegree = (derivative (R ν)).natDegree)
    (hres : ∀ ν, resultant (specAt P0 (R ν)) (derivative (specAt P0 (R ν))) ≠ 0)
    (t : E.FK) (ht : P0.ord t = 1)
    -- the coefficients λ_{i,j} of Lemma 4.2 with a = μ_ν m
    (lam : Fin r → Fin n → ℕ → E.K)
    (hlam : ∀ ν i, ∀ h ∈ LSpace (AGProxGap.divG E.liftInf (ringChar Fq ^ a ν * m)),
      (E.lift i).evalAt h =
        ∑ k ∈ Finset.range (ringChar Fq ^ a ν * m + 1), lam ν i k * localCoeff P0 t h k)
    -- a fixed irreducible factorization of the Y-primitive part of each R_{ν,P₀}
    (Hs : Fin r → Multiset (Polynomial (Polynomial E.K)))
    (hHs : ∀ ν, (∀ G ∈ Hs ν, Irreducible G) ∧ Associated (Hs ν).prod (specAt P0 (R ν)).primPart) :
    let μ : Fin r → ℕ := fun ν => ringChar Fq ^ a ν
    let zK : Fq → E.K := fun z => algebraMap Fq E.K z
    let zFK : Fq → E.FK := fun z => algebraMap Fq E.FK z
    let fK : Fq → E.FK := fun z => algebraMap F E.FK (f z)
    let S' : Finset Fq := S.filter (fun z => Cz.eval (zFK z) ≠ 0 ∧
      ∀ ν, (specAt P0 (R ν)).leadingCoeff.eval (zK z) ≠ 0 ∧
        (resultant (specAt P0 (R ν)) (derivative (specAt P0 (R ν)))).eval (zK z) ≠ 0)
    let assigned : Fq → Fin r → Prop := fun z ν =>
      evalYZ (R ν) (fK z ^ μ ν) (zFK z) = 0 ∧ ∀ ν' < ν, evalYZ (R ν') (fK z ^ μ ν') (zFK z) ≠ 0
    let y : Fq → Fin r → E.K := fun z ν => P0.evalAt (fK z) ^ μ ν
    let SνH : Fin r → Polynomial (Polynomial E.K) → Finset Fq := fun ν G =>
      S'.filter (fun z => assigned z ν ∧ evalYZ G (y z ν) (zK z) = 0)
    let Fi : Fin r → Fin n → RatYZ E.K := fun ν i =>
      Fpoly P0 t (R ν) (μ ν) m (lam ν i)
        (AGProxGap.rpoly (fun k l => algebraMap Fq E.K (u k l)) i)
    let I : Fin r → Polynomial (Polynomial E.K) → Finset (Fin n) := fun ν G =>
      Finset.univ.filter (fun i => ∃ G' : Polynomial (Polynomial E.K),
        Fi ν i = algebraMap (Polynomial (Polynomial E.K)) (RatYZ E.K) G *
          algebraMap (Polynomial (Polynomial E.K)) (RatYZ E.K) G')
    let B : Fin r → Polynomial (Polynomial E.K) → ℕ := fun ν G =>
      G.natDegree * (2 * μ ν * m * degZ (R ν) + ℓ * μ ν) + degZ G * (2 * μ ν * m * (R ν).natDegree)
    (∀ ν, ∀ G ∈ (Hs ν).toFinset, ∀ i ∈ I ν G, ∀ z ∈ SνH ν G,
      (P i).evalAt (f z) = (AGProxGap.rpoly u i).eval z) ∧
    (∀ ν, ∀ G ∈ (Hs ν).toFinset, ∀ i, i ∉ I ν G →
      ((SνH ν G).filter (fun z => (P i).evalAt (f z) = (AGProxGap.rpoly u i).eval z)).card ≤
        B ν G) ∧
    (∑ ν, ∑ G ∈ (Hs ν).toFinset, B ν G ≤ 4 * m * DY * DZ + ℓ * DY) := by sorry

end AGProxGap.Supplement
