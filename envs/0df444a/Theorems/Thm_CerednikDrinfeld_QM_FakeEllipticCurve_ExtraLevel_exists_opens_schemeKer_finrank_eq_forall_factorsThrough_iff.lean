-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_opens_schemeKer_finrank_eq_forall_factorsThrough_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_opens_schemeKer_finrank_eq_forall_factorsThrough_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/1bda687f-d276-54e5-adf2-ac921bed45bc
-- title:
--   Extra level of order N as clopen part of A[N]
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N'$, and a commutative ring $S$. Let $E$ be a fake elliptic curve of type $(\Lambda,N')$ over $S$, so in particular $E$ provides a scheme $E.A$, a structure morphism $E.f : E.A \to \operatorname{Spec} S$, a relative group law $E.L$ on $E.f$ (functorial multiplication, unit and inverse on sections over arbitrary $S$-schemes) together with the remaining data of that structure. Let $N$ be a natural number whose image in $S$ is a unit, and let $K$ be an extra level of order $N$ on $E$, i.e. a scheme $K.K$ with a morphism $K.\mathrm{levK} : K.K \to E.A$ satisfying the axioms of the structure `ExtraLevel` (closed immersion, closure under the group law, killed by $N$, $\Lambda$-stability, disjointness from `E.lev`, finiteness, flatness and local finite presentation over $S$, fibre rank $N^2$, and the prescribed geometric fibres $\mathbb{Z}/N \times \mathbb{Z}/N$). The assertion is that there exists an open subscheme $U$ of the kernel scheme $E.L.\mathrm{schemeKer}\,N$, the fibre product of the multiplication-by-$N$ morphism $E.L.\mathrm{schemeNsmul}\,N : E.A \to E.A$ with the unit section $\operatorname{Spec} S \to E.A$, such that: the underlying set of $U$ is closed, so $U$ is a clopen part of that kernel; the composite of the open immersion $U.\iota$ with the projection $E.L.\mathrm{schemeKerStr}\,N$ to $\operatorname{Spec} S$ has fibre rank $N^2$ at every point of $\operatorname{Spec} S$; and for every scheme $T$, every morphism $t : T \to \operatorname{Spec} S$ and every $T$-point $P$ of $E.A$ over $t$ (a morphism $T \to E.A$ whose composite with $E.f$ is $t$), $P$ factors through $K.\mathrm{levK}$ if and only if $P$ factors through $U.\iota$ followed by the first pullback projection to $E.A$.
--
--   This is the easy half of the dictionary between extra level structures of order $N$ on a fake elliptic curve and admissible clopen subgroup schemes of its $N$-torsion, in the style of the representability discussion for level structures on elliptic curves: when $N$ is invertible on the base the $N$-torsion is finite étale, and a finite flat closed subgroup scheme of it is automatically an open-and-closed part with the same points. It is used in the construction of fake elliptic curves with full level structure, where extra levels have to be represented by finite étale data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_opens_schemeKer_finrank_eq_forall_factorsThrough_iff.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_opens_schemeKer_finrank_eq_forall_factorsThrough_iff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N' : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N' S) (N : ℕ) (hN : IsUnit ((N : ℕ) : S)) (K : E.ExtraLevel N) :
    ∃ U : (E.L.schemeKer N).Opens, IsClosed (U : Set ↥(E.L.schemeKer N)) ∧
      (∀ s : ↥(Spec (CommRingCat.of S)), (U.ι ≫ E.L.schemeKerStr N).finrank s = N ^ 2) ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
        FactorsThrough K.levK P ↔
          FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P := by sorry
