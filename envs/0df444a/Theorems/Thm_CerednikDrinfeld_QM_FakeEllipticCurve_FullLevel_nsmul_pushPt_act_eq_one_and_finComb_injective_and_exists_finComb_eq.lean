-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_nsmul_pushPt_act_eq_one_and_finComb_injective_and_exists_finComb_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.nsmul_pushPt_act_eq_one_and_finComb_injective_and_exists_finComb_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/58400aad-be6c-5da2-905d-fe802b3226e0
-- title:
--   Translation of a full level-m structure into 2g torsion sections
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order, i.e. contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$ and is finitely generated. Let $N\in\mathbb{N}$, let $S$ be a commutative ring, let $E$ be a fake elliptic curve for $\Lambda$ of level $N$ over $S$ — an abelian scheme $f:A\to\operatorname{Spec}S$ of relative fibre dimension $2$ with commutative relative group law $E.L$ and an action of $\Lambda$ by endomorphisms over the base, with the further data of that structure — let $m$ be a nonzero natural number and let $FL$ be a full level-$m$ structure on $E$, whose underlying datum is a section $FL.P$ of $f$ over the identity of $\operatorname{Spec}S$. Let $\beta:\mathrm{Fin}\,4\to\Lambda$ be such that every $x\in\Lambda$ is $\sum_j c_j\beta_j$ for a unique $c:\mathrm{Fin}\,4\to\mathbb{Z}$, i.e. $\beta$ is a $\mathbb{Z}$-basis of $\Lambda$. Put $P_i$ for the push-forward of $FL.P$ along the endomorphism $E.\mathrm{act}(\beta_i)$. The conclusion is the conjunction of three assertions: (i) $m\cdot P_i$ is the identity section for each of the four $i$, for the iterated group law $E.L.\mathrm{nsmul}$; (ii) for every algebraically closed field $k$ and ring homomorphism $sk:S\to k$, the map sending $c:\mathrm{Fin}\,4\to\mathrm{Fin}\,m$ to the combination $E.L.\mathrm{finComb}$ of the base changes of the $P_i$ along $\operatorname{Spec}(sk)$ with exponents $c_i$ — the product $\prod_i P_i^{c_i}$ in the group of $k$-points — is injective; (iii) for every such $k$ and $sk$, every point $Q$ of $A$ over $\operatorname{Spec}(sk)$ killed by $m$ equals such a combination for some $c:\mathrm{Fin}\,4\to\mathrm{Fin}\,m$.
--
--   This converts a full level-$m$ structure on a fake elliptic curve, formulated through the $\Lambda$-action on one section, into the currency of a polarised abelian scheme with level structure: the three clauses are exactly the fields `P_torsion`, `P_indep` and `P_span` of `PolarisedAbelianScheme` for $g=2$ and level $m$, with the $2g=4$ sections given by a $\mathbb{Z}$-basis of $\Lambda$ acting on $FL.P$. It is used in assembling quaternionic moduli data, by [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_packages_of_withFullLevel_of_isUnit_two`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_packages_of_withFullLevel_of_isUnit_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_nsmul_pushPt_act_eq_one_and_finComb_injective_and_exists_finComb_eq.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.nsmul_pushPt_act_eq_one_and_finComb_injective_and_exists_finComb_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (m : ℕ) [NeZero m] (FL : E.FullLevel m)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j) :
    (∀ i : Fin (2 * 2), E.L.nsmul (𝟙 (Spec (CommRingCat.of S))) m (pushPt (E.act (β i)) (E.act_over (β i)) FL.P) = E.L.one (𝟙 (Spec (CommRingCat.of S)))) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (c c' : Fin (2 * 2) → Fin m),
      E.L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (pushPt (E.act (β i)) (E.act_over (β i)) FL.P)) (fun i => (c i : ℕ)) =
        E.L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (pushPt (E.act (β i)) (E.act_over (β i)) FL.P)) (fun i => (c' i : ℕ)) →
        c = c') ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) E.f),
      E.L.nsmul (Spec.map (CommRingCat.ofHom sk)) m Q = E.L.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ c : Fin (2 * 2) → Fin m,
          E.L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (pushPt (E.act (β i)) (E.act_over (β i)) FL.P)) (fun i => (c i : ℕ)) = Q) := by sorry
