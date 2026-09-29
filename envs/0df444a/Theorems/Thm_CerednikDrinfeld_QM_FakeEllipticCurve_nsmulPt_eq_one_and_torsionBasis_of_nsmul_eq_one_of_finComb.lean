-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_one_and_torsionBasis_of_nsmul_eq_one_of_finComb
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nsmulPt_eq_one_and_torsionBasis_of_nsmul_eq_one_of_finComb
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/60f41585-924b-5a90-a7da-794d3ae4c286
-- title:
--   Full level-m structure yields a torsion basis
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $S$, a fake elliptic curve $E$ of type $(\Lambda,N)$ over $S$ with relative group law $E.L$ on $E.f : E.A \to \operatorname{Spec} S$, and a nonzero natural number $m$. Let $Q : \mathrm{Fin}\,(2\cdot 2) \to \mathrm{SchemeHomOver}\,(\mathbb{1})\,E.f$ be four sections of $E.f$ over $S$ such that: (htor) each $Q_i$ satisfies $E.L.\mathrm{nsmul}\ m\,(Q_i) = E.L.\mathrm{one}$; (hind) for every algebraically closed field $k$ and every ring homomorphism $sk : S \to k$, the map sending $c : \mathrm{Fin}\,4 \to \mathrm{Fin}\,m$ to $E.L.\mathrm{finComb}$ of the base-changed $Q_i$ with exponents $c_i$ (the ordered product $\prod_i Q_i^{c_i}$ in the group of $k$-points) is injective; (hspan) over each such $k$, every point $R$ of $E$ over $\operatorname{Spec} k$ with $E.L.\mathrm{nsmul}\ m\,R = E.L.\mathrm{one}$ equals such a $\mathrm{finComb}$ for some $c$ with values in $\mathrm{Fin}\,m$. The conclusion is the conjunction: (i) $\mathrm{nsmulPt}\,E.L\,\mathbb{1}\,m\,(Q_i) = E.L.\mathrm{one}$ for all $i : \mathrm{Fin}\,4$; and (ii) for every algebraically closed field $k$ and $sk : S \to k$, first, every $m$-torsion point $R$ over $\mathrm{geomPoint}\,k\,sk$ is the bracketed four-fold product $(((Q_0^{n_0}\cdot Q_1^{n_1})\cdot Q_2^{n_2})\cdot Q_3^{n_3})$, formed with $E.L.\mathrm{mul}$ and $\mathrm{nsmulPt}$ from the specialisations $\mathrm{sectionAt}\,(Q_i)\,k\,sk$, for some $n : \mathrm{Fin}\,4 \to \mathbb{N}$; and second, if such a product equals $E.L.\mathrm{one}$ then $m \mid n_i$ for every $i$.
--
--   This converts a full level-$m$ structure stated in the shape used for polarised abelian schemes (torsion killed by $m$, with $\mathrm{finComb}$ over exponents in $\mathrm{Fin}\,m$ injective and surjective onto the geometric $m$-torsion) into the shape of a torsion basis used for fake elliptic curves (recursive $\mathrm{nsmulPt}$ multiples, an explicit four-fold product with arbitrary natural exponents, and a divisibility condition in place of injectivity). It is used in the construction of quaternionic-multiplication packages with full level structure, [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_withFullLevel_packages`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_withFullLevel_packages).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_one_and_torsionBasis_of_nsmul_eq_one_of_finComb.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nsmulPt_eq_one_and_torsionBasis_of_nsmul_eq_one_of_finComb
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (m : ℕ) [NeZero m]
    (Q : Fin (2 * 2) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (htor : ∀ i : Fin (2 * 2), E.L.nsmul (𝟙 (Spec (CommRingCat.of S))) m (Q i) = E.L.one (𝟙 (Spec (CommRingCat.of S))))
    (hind : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (c c' : Fin (2 * 2) → Fin m),
      E.L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (Q i)) (fun i => (c i : ℕ)) =
        E.L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (Q i)) (fun i => (c' i : ℕ)) →
        c = c')
    (hspan : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (R : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) E.f),
      E.L.nsmul (Spec.map (CommRingCat.ofHom sk)) m R = E.L.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ c : Fin (2 * 2) → Fin m,
          E.L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (Q i)) (fun i => (c i : ℕ)) = R) :

      (∀ i : Fin 4, nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m (Q i) = E.L.one (𝟙 (Spec (CommRingCat.of S)))) ∧

      (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
        (∀ R : SchemeHomOver (geomPoint k sk) E.f, nsmulPt E.L (geomPoint k sk) m R = E.L.one (geomPoint k sk) →
          ∃ n : Fin 4 → ℕ,
            E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk)
              (nsmulPt E.L (geomPoint k sk) (n 0) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 0)) (nsmulPt E.L (geomPoint k sk) (n 1) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 1)))
              (nsmulPt E.L (geomPoint k sk) (n 2) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 2))) (nsmulPt E.L (geomPoint k sk) (n 3) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 3)) = R) ∧
        (∀ n : Fin 4 → ℕ,
            E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk)
              (nsmulPt E.L (geomPoint k sk) (n 0) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 0)) (nsmulPt E.L (geomPoint k sk) (n 1) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 1)))
              (nsmulPt E.L (geomPoint k sk) (n 2) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 2))) (nsmulPt E.L (geomPoint k sk) (n 3) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 3)) = E.L.one (geomPoint k sk) →
          ∀ i : Fin 4, m ∣ n i)) := by sorry
