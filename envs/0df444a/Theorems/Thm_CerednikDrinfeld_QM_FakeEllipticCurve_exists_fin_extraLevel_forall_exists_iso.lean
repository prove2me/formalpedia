-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fin_extraLevel_forall_exists_iso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fin_extraLevel_forall_exists_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/e9546c68-5679-5f5d-a88d-d1517704619d
-- title:
--   Finitely many extra levels at ℓ up to isomorphism
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N$ (nonzero) and $\ell$ with $\ell$ prime, and an algebraically closed field $k$ in which $\ell \neq 0$. Let $E$ be a fake elliptic curve of level $N$ with $\Lambda$-action over $k$, that is, a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} k$ carrying a commutative relative group law $L$ on functorial points, the abelian-scheme property bundle, fibres of Krull dimension $2$, an action of $\Lambda$ by endomorphisms over $\operatorname{Spec} k$ that are additive for $L$, multiplicative in $\Lambda$ and satisfy the reduced-trace condition on tangent spaces, together with a level-$N$ subscheme $\mathrm{lev}$. An extra level at $\ell$ on $E$ is a closed immersion $\mathrm{levK} : K \to A$ whose points are closed under multiplication and inversion, contain the unit, are killed by $\ell$, are stable under the $\Lambda$-action and meet the points of $\mathrm{lev}$ only in the unit, with $\mathrm{levK}$ followed by $f$ finite, flat and locally of finite presentation of fibre rank $\ell^2$, and with geometric fibres isomorphic as groups to $\mathbb{Z}/\ell \times \mathbb{Z}/\ell$ when $\ell$ is invertible. The conclusion is that there are an $n : \mathbb{N}$ and extra levels $K_1,\dots,K_n$ at $\ell$ on $E$ such that every extra level $K'$ at $\ell$ satisfies $(E,K') \cong (E,K_i)$ for some $i$, where the isomorphism relation on pairs asks for an isomorphism $e$ of the underlying scheme over $\operatorname{Spec} k$ compatible with the group laws, commuting with the $\Lambda$-action, and matching both the level-$N$ subschemes and the extra-level subschemes on points.
--
--   This is the finiteness statement that the set of extra $\ell$-level structures on a fixed fake elliptic curve over an algebraically closed field has only finitely many isomorphism classes of pairs; it is uniform in $\ell$ and carries no count of the classes. It feeds the finiteness of the degeneracy morphism for the coarse moduli problem, [`CerednikDrinfeld.QM.IsCoarseModuliT.isFinite_degeneracy`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.isFinite_degeneracy).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fin_extraLevel_forall_exists_iso.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open AlgebraicCurve
open CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fin_extraLevel_forall_exists_iso
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) [NeZero N] (hℓ : ℓ.Prime)
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) :
    ∃ (n : ℕ) (K : Fin n → E.ExtraLevel ℓ), ∀ K' : E.ExtraLevel ℓ, ∃ i : Fin n,
      FakeEllipticCurve.WithExtraLevel.Iso (⟨E, K'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) ⟨E, K i⟩ := by sorry
