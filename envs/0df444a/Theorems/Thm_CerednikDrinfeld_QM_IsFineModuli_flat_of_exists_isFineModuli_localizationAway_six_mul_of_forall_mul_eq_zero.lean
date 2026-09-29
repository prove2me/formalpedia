-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_flat_of_exists_isFineModuli_localizationAway_six_mul_of_forall_mul_eq_zero
-- name    : CerednikDrinfeld.QM.IsFineModuli.flat_of_exists_isFineModuli_localizationAway_six_mul_of_forall_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/e97b9e66-814c-5fe9-aa28-ffb2a231b13f
-- title:
--   Flatness of fine moduli over any base from a torsion-free model over ℤ[1/6Nm]
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and nonzero natural numbers $N,m$. Assume, as hypothesis $h$, that there exist a scheme $M_0$, a morphism $\pi_0 : M_0 \to \operatorname{Spec}\mathbb{Z}[1/(6Nm)]$ (the localisation of $\mathbb{Z}$ away from the integer $6Nm$) and a family of maps $\mathrm{ptF}_0$ sending each commutative ring $S$, each morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathbb{Z}[1/(6Nm)]$ and each pair consisting of a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ data together with a full level-$m$ structure on it, to a morphism $\operatorname{Spec} S \to M_0$ over $s$, such that `IsFineModuli` holds for $(M_0,\pi_0,\mathrm{ptF}_0)$ — that is, $\mathrm{ptF}_0$ is invariant under isomorphism of such data, compatible with pullback along ring homomorphisms, surjective onto morphisms over $s$, and injective up to isomorphism — and such that moreover the sections over every affine open $U \subseteq M_0$ have no $\mathbb{Z}$-torsion: for $z \in \mathbb{Z}$ nonzero and $s \in \Gamma(M_0,U)$, $z\,s = 0$ forces $s = 0$. Let $\mathcal{O}$ be a commutative ring in which the images of $N$, $m$, $2$ and $3$ are units, and let $M$, $\pi_M : M \to \operatorname{Spec}\mathcal{O}$ and $\mathrm{ptF}$ satisfy `IsFineModuli` for the same moduli problem over $\mathcal{O}$. Then $\pi_M$ is flat.
--
--   This is the formal reduction step for flatness of the fine moduli scheme of fake elliptic curves with $\Lambda$-action, level-$N$ and full level-$m$ structure: flatness over an arbitrary base in which $6Nm$ is invertible follows from the existence of a single model over $\mathbb{Z}[1/(6Nm)]$ whose affine coordinate rings are $\mathbb{Z}$-torsion-free. It is invoked by [`CerednikDrinfeld.QM.IsFineModuli.flat_of_isUnit_of_isUnit_two_of_isUnit_three`](thm.html#CerednikDrinfeld.QM.IsFineModuli.flat_of_isUnit_of_isUnit_two_of_isUnit_three), and the proof uses only the base-change and uniqueness properties of fine moduli, namely [`CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_of_isPullback`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_of_isPullback) and [`CerednikDrinfeld.QM.IsFineModuli.exists_iso_of_isFineModuli`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_iso_of_isFineModuli).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_flat_of_exists_isFineModuli_localizationAway_six_mul_of_forall_mul_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.flat_of_exists_isFineModuli_localizationAway_six_mul_of_forall_mul_eq_zero
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) [NeZero N] [NeZero m]
    (h : ∃ (M₀ : Scheme.{0}) (π₀ : M₀ ⟶ Spec (CommRingCat.of (Localization.Away ((6 * N * m : ℕ) : ℤ))))
      (ptF₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((6 * N * m : ℕ) : ℤ)))),
        FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s π₀),
      IsFineModuli Λ N m M₀ π₀ ptF₀ ∧
        ∀ (U : M₀.affineOpens) (z : ℤ) (s : Γ(M₀, U)), z ≠ 0 → (z : Γ(M₀, U)) * s = 0 → s = 0)
    (𝒪 : Type) [CommRing 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪))
    (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF) :
    Flat πM := by sorry
