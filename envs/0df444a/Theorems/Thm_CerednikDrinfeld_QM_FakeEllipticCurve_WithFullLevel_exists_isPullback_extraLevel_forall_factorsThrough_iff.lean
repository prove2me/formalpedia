-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_extraLevel_forall_factorsThrough_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_factorsThrough_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/4a63545e-2680-50f3-af8d-b426983ea42e
-- title:
--   Base change of full level-m and extra level-ℓ structures
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, naturals $N$, $m$, $\ell$ with $\ell$ prime and $\ell \mid m$, a further $\mathbb{Z}$-submodule $L_0$, commutative rings $S$, $S'$ and a ring homomorphism $\varphi : S \to S'$ with $m$ a unit in $S$. Let $w = (E, P)$ consist of a fake elliptic curve $E$ over $S$ for $(\Lambda, N)$ together with a full level-$m$ structure, and let $K$ be an extra level structure at $\ell$ on $E$, with closed immersion $\mathrm{levK} : K \to E.A$. The conclusion asserts the existence of $w' = (E', P')$ over $S'$ and an extra level $K'$ at $\ell$ on $E'$ such that: (i) `WithFullLevel.IsPullback` holds for $\varphi$, i.e. there is $g : E'.A \to E.A$ making the square of $E'.f$, $E.f$ and $\mathrm{Spec}\,\varphi$ cartesian, compatible with the relative group laws on $T$-points, $\Lambda$-equivariant, carrying points factoring through $\mathrm{lev}'$ to points factoring through $\mathrm{lev}$, and satisfying $P'.1 \circ g = g \circ (\mathrm{Spec}\,\varphi)$ in diagrammatic order; (ii) the analogous `WithExtraLevel.IsPullback` for $(E,K)$ and $(E',K')$, whose cartesian morphism is again only asserted to exist, with the factoring condition imposed for both $\mathrm{lev}$ and $\mathrm{levK}$; and (iii) the implication that if, for every algebraically closed field $k$, every $sk : S \to k$ and every point $Q$ of $E.A$ over $\mathrm{geomPoint}\,k\,sk$, factoring through $K.\mathrm{levK}$ is equivalent to $Q = x \cdot \big((m/\ell)\,P(sk)\big)$ for some $x \in \Lambda \cap L_0$ (natural-number division $m/\ell$, $x$ acting by $E.\mathrm{act}$), then the same description of $K'.\mathrm{levK}$ holds at every geometric point of $S'$.
--
--   This is the base-change compatibility for the moduli problem of fake elliptic curves with a full level-$m$ structure and an extra level structure at $\ell$, asserting that the triple $(E, P, K)$ admits a pullback along any ring homomorphism and that the description of the extra level as the orbit $L_0 \cdot (m/\ell) P$ at geometric points is preserved. It is used in establishing the fine moduli property, via [`CerednikDrinfeld.QM.IsFineModuli.existsUnique_hom_ptT_comp_eq`](thm.html#CerednikDrinfeld.QM.IsFineModuli.existsUnique_hom_ptT_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_extraLevel_forall_factorsThrough_iff.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_factorsThrough_iff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m) (L₀ : Submodule ℤ ℍ[ℚ, a, b])
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (hm : IsUnit ((m : ℕ) : S))
    (w : FakeEllipticCurve.WithFullLevel Λ N m S) (K : w.1.ExtraLevel ℓ) :
    ∃ (w' : FakeEllipticCurve.WithFullLevel Λ N m S') (K' : w'.1.ExtraLevel ℓ),
      FakeEllipticCurve.WithFullLevel.IsPullback φ w w' ∧
      FakeEllipticCurve.WithExtraLevel.IsPullback φ (⟨w.1, K⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) ⟨w'.1, K'⟩ ∧
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) w.1.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w.1.act x) (w.1.act_over x)
              (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = Q) →
        ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (Q : SchemeHomOver (geomPoint k sk) w'.1.f),
        FactorsThrough K'.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w'.1.act x) (w'.1.act_over x)
              (nsmulPt w'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w'.2.P k sk)) = Q) := by sorry
