-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_extraLevel_forall_geomPoint_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_geomPoint_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/1915885c-bd93-556d-b50f-c65a2d948c9a
-- title:
--   Base change of fake elliptic curves with full and extra level
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N$, $m$, $\ell$, commutative rings $S$, $S'$ and a ring homomorphism $\varphi : S \to S'$. Let $w = (E, P)$ consist of a fake elliptic curve $E$ over $S$ of level $N$ (a scheme $E.A$ over $\operatorname{Spec} S$ with relative commutative group law $E.L$, two-dimensional fibres, a $\Lambda$-action by $E.f$-morphisms compatible with the group law and the trace condition, and the level datum $E.\mathrm{lev}$) together with a full level-$m$ structure $P$, and let $K$ be an extra level-$\ell$ structure on $E$: a closed immersion $K.\mathrm{levK} : K.K \to E.A$ whose $T$-points are closed under multiplication and inversion, contain the identity, are killed by $\ell$, are stable under the $\Lambda$-action, meet those factoring through $E.\mathrm{lev}$ only in the identity, and which is finite, flat and locally of finite presentation of fibre rank $\ell^2$, geometrically isomorphic as a group to $(\mathbb{Z}/\ell)^2$ whenever $\ell$ is invertible. Then there exist a pair $w' = (E', P')$ over $S'$ and an extra level-$\ell$ structure $K'$ on $E'$ such that: $w'$ is a pullback of $w$ along $\varphi$, i.e. there is $g : E'.A \to E.A$ making $E'.f$, $E.f$, $\operatorname{Spec}\varphi$ a cartesian square, compatible with the group laws on $T$-points, satisfying $E'.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for all $x \in \Lambda$, carrying points factoring through $E'.\mathrm{lev}$ to points factoring through $E.\mathrm{lev}$ after composition with $g$, and with $P'$ followed by $g$ equal to $\operatorname{Spec}\varphi$ followed by $P$; the pair $(E', K')$ is a pullback of $(E, K)$ along $\varphi$ in the same sense, with the extra clause for $\mathrm{levK}$; and, for every $\mathbb{Z}$-submodule $L_0 \subseteq \mathbb{H}[\mathbb{Q},a,b]$, every algebraically closed field $k$ and every ring map $sk : S' \to k$, the assertion that every point $Q$ of $E$ over the geometric point $sk \circ \varphi$ factors through $K.\mathrm{levK}$ if and only if $Q$ is of the form $x \cdot \bigl((m/\ell)\,P_{sk\circ\varphi}\bigr)$ for some $x \in \Lambda$ lying in $L_0$ holds if and only if the corresponding assertion holds for $E'$, $K'$, $P'$ over the geometric point $sk$. Here $m/\ell$ is natural-number division and the multiple is iterated multiplication for the relative group law.
--
--   This is the base-change step for the fine moduli problem of fake elliptic curves with a full level-$m$ structure and an auxiliary level-$\ell$ subgroup scheme, in the form in which the description of the extra level as the $\Lambda$-orbit of $(m/\ell)$-multiples of the universal point transfers, geometric point by geometric point, across the cartesian square. It is used in the construction of flat surjective covers with full level structure, via [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_extraLevel_forall_geomPoint_iff.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_geomPoint_iff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (m ℓ : ℕ)
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (w : FakeEllipticCurve.WithFullLevel Λ N m S) (K : w.1.ExtraLevel ℓ) :
    ∃ (w' : FakeEllipticCurve.WithFullLevel Λ N m S') (K' : w'.1.ExtraLevel ℓ),
      FakeEllipticCurve.WithFullLevel.IsPullback φ w w' ∧
      FakeEllipticCurve.WithExtraLevel.IsPullback φ (⟨w.1, K⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) ⟨w'.1, K'⟩ ∧
      ∀ (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k),
        (∀ Q : SchemeHomOver (geomPoint k (sk.comp φ)) w.1.f,
          FactorsThrough K.levK Q ↔
            ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
              pushPt (w.1.act x) (w.1.act_over x)
                (nsmulPt w.1.L (geomPoint k (sk.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k (sk.comp φ))) = Q) ↔
        (∀ Q : SchemeHomOver (geomPoint k sk) w'.1.f,
          FactorsThrough K'.levK Q ↔
            ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
              pushPt (w'.1.act x) (w'.1.act_over x)
                (nsmulPt w'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w'.2.P k sk)) = Q) := by sorry
