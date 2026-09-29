-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_ringHom
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/b16209ee-a230-5ca4-ae30-8d858a32f342
-- title:
--   Invariance of the C-factorisation condition under extension of k
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,m$, a commutative ring $S$, and an element $u$ of `FakeEllipticCurve.WithFullLevel Λ N m S`, that is a pair consisting of a fake elliptic curve $E=u.1$ over $S$ (with total space $u.1.A$, structure morphism $u.1.f$, relative group law $u.1.L$, action $x\mapsto u.1.\mathrm{act}\,x$ of $\Lambda$ by endomorphisms over $S$, and auxiliary morphism $u.1.\mathrm{lev} : u.1.C \to u.1.A$) together with a full level-$m$ structure $u.2$ whose underlying datum is a section $u.2.P$ of $u.1.f$ over the identity of $\operatorname{Spec} S$. Let $k$ be an algebraically closed field with a ring homomorphism $sk : S \to k$, let $K$ be an algebraically closed field with a ring homomorphism $\iota : k \to K$, let $L_0$ be a further $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ and let $n$ be a natural number. Write $\bar s = \operatorname{Spec}(sk)$ and $\bar s_K = \operatorname{Spec}(\iota\circ sk)$ for the associated geometric points of $\operatorname{Spec} S$, and for a geometric point $t$ let $P_t$ denote the $n$-fold iterate, under the group law $u.1.L$ over $t$, of the pullback of $u.2.P$ along $t$ (the $n=0$ case being the identity section $u.1.L.\mathrm{one}\,t$). The assertion is the equivalence of the following two statements: for every $x \in \Lambda$ with $x \in L_0$, if the point $u.1.\mathrm{act}\,x$ applied to $P_{\bar s}$ factors through $u.1.\mathrm{lev}$, i.e. there is a morphism $\operatorname{Spec} k \to u.1.C$ whose composite with $u.1.\mathrm{lev}$ is that point, then this point equals $u.1.L.\mathrm{one}\,\bar s$; and the same statement with $k,\bar s$ replaced throughout by $K,\bar s_K$.
--
--   The condition appearing on both sides is the pointwise level condition used in the fine-moduli description of the curves parametrising fake elliptic curves with level structure; the theorem says that it is insensitive to enlarging the algebraically closed field through which the geometric point is taken. It is used in the comparison of the condition with a level-$m$ translate of the full level structure and in the criterion for the locus where it holds to be cut out by a closed subscheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_ringHom.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_ringHom
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {S : Type u} [CommRing S]
    (u : FakeEllipticCurve.WithFullLevel Λ N m S)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (K : Type u) [Field K] [IsAlgClosed K] (ι : k →+* K)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (n : ℕ) :
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt u.2.P k sk))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt u.2.P k sk)) = u.1.L.one (geomPoint k sk)) ↔
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint K (ι.comp sk)) n (FakeEllipticCurve.sectionAt u.2.P K (ι.comp sk)))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint K (ι.comp sk)) n (FakeEllipticCurve.sectionAt u.2.P K (ι.comp sk))) = u.1.L.one (geomPoint K (ι.comp sk))) := by sorry
