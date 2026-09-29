-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_finrank_kernel_verschiebung_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_finrank_kernel_verschiebung_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/e2bfc7f4-d10e-50ee-ac65-8dc9e94ff490
-- title:
--   Kernel of Verschiebung is finite of rank ℓ²
-- statement:
--   Let $k$ be an algebraically closed field of characteristic a prime $\ell$, and let $E$ and $E_\ell$ be fake elliptic curves over $k$ for the lattice $\Lambda$ in the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and level $N$: each consists of a scheme over $\operatorname{Spec} k$ carrying a commutative relative group law, smooth, proper with connected fibres, with all fibres of topological Krull dimension $2$, together with an action of $\Lambda$ by group-law endomorphisms satisfying the expected multiplicativity and trace conditions, and level data. Let $D$ be a Frobenius–Verschiebung datum for $\ell$, $E$, $E_\ell$: it provides a morphism $\mathrm{pr} : E_\ell.A \to E.A$ exhibiting $E_\ell.f$ as the base change of $E.f$ along $\operatorname{Spec}$ of the Frobenius of $k$, compatibly with the group laws, the $\Lambda$-action and the level maps; morphisms $F : E.A \to E_\ell.A$ and $V : E_\ell.A \to E.A$ over $\operatorname{Spec} k$ that are homomorphisms for the relative group laws, commute with the $\Lambda$-action and preserve factorisation through the level maps; and further fields `F_frobenius` and `V_F`, identifying $F$ followed by $\mathrm{pr}$ with absolute Frobenius on points over rings of characteristic $\ell$, and $F$ followed by $V$ with multiplication by $\ell$ for $E.L$. Then the projection from the fibre product of $V$ with the identity section $E.L.\mathrm{one}$ over $\operatorname{Spec} k$, followed by $E_\ell.f$ — that is, the structure morphism of the scheme-theoretic kernel of $V$ — is finite, locally of finite presentation, and has `finrank` equal to $\ell^2$ at every point of $\operatorname{Spec} k$.
--
--   This is the degree computation for the Verschiebung of a fake elliptic curve in characteristic $\ell$: an abelian surface has $\deg F = \ell^2$ and $VF = [\ell]$ of degree $\ell^4$, so $\ker V$ is finite flat of rank $\ell^2$. It supplies the geometric input for the statement that $\ker V$ furnishes an extra level structure, and is used in bounding the number of torsion points in the supersingular analysis behind the Cherednik–Drinfeld description of $X_0^{qq'}(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_finrank_kernel_verschiebung_eq.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_finrank_kernel_verschiebung_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ) :
    IsFinite (pullback.fst D.V (E.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ Eℓ.f) ∧
      LocallyOfFinitePresentation (pullback.fst D.V (E.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ Eℓ.f) ∧
      ∀ s : ↥(Spec (CommRingCat.of k)), (pullback.fst D.V (E.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ Eℓ.f).finrank s = ℓ ^ 2 := by sorry
