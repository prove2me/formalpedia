-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer_of_level
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/e42697d4-9fb2-5b8b-8cf2-1ab90be16224
-- title:
--   Closed-open subgroup of N-torsion is an extra level
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N_0$, a commutative ring $S$, and a fake elliptic curve $E$ of level $N_0$ over $S$ with $\Lambda$-action, with abelian scheme $E.f : E.A \to \operatorname{Spec} S$, relative group law $E.L$ and level-structure morphism $E.\mathrm{lev}$. Let $N$ be a nonzero natural number which is a unit in $S$, and let $U$ be an open subscheme of the $N$-torsion $E.L.\mathrm{schemeKer}\,N$ (the pullback of the multiplication-by-$N$ morphism along the unit section) whose underlying set is also closed. Write $\iota_U$ for the composite of the open immersion $U.\iota$ with the first projection to $E.A$, and say a point $P$ of $E.A$ over $t : T \to \operatorname{Spec} S$ (a morphism $T \to E.A$ over $t$) factors through $U$ if $P$ is $\iota_U$ precomposed with some $T \to U$. Assume: (i) for every $t$, the points factoring through $U$ are closed under $E.L.\mathrm{mul}$ and $E.L.\mathrm{inv}$; (ii) $E.L.\mathrm{one}\,t$ factors through $U$; (iii) for each $x \in \Lambda$, pushing a point factoring through $U$ forward along $E.\mathrm{act}\,x$ again factors through $U$; (iv) a point factoring through both $U$ and $E.\mathrm{lev}$ is the unit; (v) the structure morphism $U \to \operatorname{Spec} S$ has rank $N^2$ at every point; (vi) for every algebraically closed field $k$ and ring homomorphism $sk : S \to k$ with $N \neq 0$ in $k$, there is a bijection $\mathbb{Z}/N \times \mathbb{Z}/N \simeq \{P$ over $\operatorname{geomPoint}\,k\,sk$ factoring through $U\}$ carrying addition to $E.L.\mathrm{mul}$. Then there exists an extra level $K$ of order $N$ on $E$ such that, for every $t : T \to \operatorname{Spec} S$ and every point $P$ over $t$, $P$ factors through $K.\mathrm{levK}$ if and only if $P$ factors through $U$.
--
--   This is the recognition criterion saying that a closed-and-open subgroup scheme of the $N$-torsion of a fake elliptic curve of level $N_0$, of rank $N^2$ with geometric fibres $(\mathbb{Z}/N)^2$ and meeting the given level structure only in the unit section, is an extra level structure of order $N$ in the sense of the `ExtraLevel` bundle; finiteness, flatness and finite presentation come from finite étaleness of the $N$-torsion when $N$ is invertible. It is used to produce extra level structures on fake elliptic curves with full level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer_of_level.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer_of_level
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N₀ : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N₀ S) (N : ℕ) [NeZero N] (hN : IsUnit ((N : ℕ) : S))
    (U : (E.L.schemeKer N).Opens) (hUc : IsClosed (U : Set ↥(E.L.schemeKer N)))
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P →
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) Q →
        FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
            (E.L.mul t P Q) ∧
          FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
            (E.L.inv t P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)),
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
        (E.L.one t))
    (hstab : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P →
        FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
          (pushPt (E.act x) (E.act_over x) P))
    (hdisj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P →
        FactorsThrough E.lev P → P = E.L.one t)
    (hrank : ∀ s : ↥(Spec (CommRingCat.of S)), (U.ι ≫ E.L.schemeKerStr N).finrank s = N ^ 2)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), (N : k) ≠ 0 →
      ∃ e : ZMod N × ZMod N ≃
          {P : SchemeHomOver (geomPoint k sk) E.f //
            FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) E.f) = E.L.mul (geomPoint k sk) (e x) (e y)) :
    ∃ K : E.ExtraLevel N,
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
        FactorsThrough K.levK P ↔
          FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P := by sorry
