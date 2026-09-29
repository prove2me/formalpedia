-- Prove2me | Theorems.Thm_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_pt_frobeniusTwist_eq_specMap_frobenius_comp_pt
-- name    : CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.pt_frobeniusTwist_eq_specMap_frobenius_comp_pt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/74ece463-15be-5266-8c55-c8aaf87114ff
-- title:
--   Moduli point of a Frobenius twist over ℤ[1/D]
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $R$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a $\mathbb{Q}$-algebra map $\iota$ from that algebra to $M_2(\mathbb{R})$, a family $\mathcal{S}$ of sets of units of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$, a Shimura curve model $M$ for these data, a further submodule $\Lambda$, naturals $N,q,q',D$, and a moduli witness $w : M.\mathrm{ModuliWitnessD}\ \Lambda\ N\ q\ q'\ D$; thus $w$ provides an integral scheme $X$, a smooth proper morphism $\pi_X : X \to \operatorname{Spec}(\mathbb{Z}[1/D])$ (the localisation of $\mathbb{Z}$ away from $D$), and for every commutative ring $S$ with a morphism $s$ from $\operatorname{Spec} S$ to that base a map $\mathrm{pt}$ sending a fake elliptic curve over $S$ to an $S$-point of $X$ over $s$. Let $k$ be a field of characteristic a prime $\ell$, let $sk$ be a morphism from $\operatorname{Spec} k$ to $\operatorname{Spec}(\mathbb{Z}[1/D])$, and let $\bar A$, $\bar A_\ell$ be fake elliptic curves over $k$ (abelian-scheme property bundles of relative dimension two with commutative relative group law, $\Lambda$-action and level data) admitting a Frobenius–Verschiebung datum for $\ell$: a morphism $\mathrm{pr} : \bar A_\ell.A \to \bar A.A$ making the square over $\operatorname{Spec}$ of the $\ell$-power Frobenius of $k$ cartesian and compatible with the group laws, the $\Lambda$-actions and the level structures, together with morphisms $F : \bar A.A \to \bar A_\ell.A$ and $V : \bar A_\ell.A \to \bar A.A$ over $k$ which are homomorphisms for the relative group laws, commute with the $\Lambda$-actions and preserve the level structures, and further compatibilities. The conclusion is that the underlying morphism $\operatorname{Spec} k \to X$ of $\mathrm{pt}(\bar A_\ell)$ equals $\operatorname{Spec}$ of the Frobenius $x \mapsto x^\ell$ of $k$ followed by the underlying morphism of $\mathrm{pt}(\bar A)$.
--
--   This is the moduli-theoretic description of Frobenius: on the integral model of the Shimura curve, passing to the Frobenius twist of a fake elliptic curve over a field of characteristic $\ell$ amounts to precomposing its moduli point with $\operatorname{Spec}$ of the Frobenius of $k$. It feeds the computation of the action of Frobenius on divisors and places used in the Čerednik–Drinfeld comparison, being cited by [`CerednikDrinfeld.ShimuraCurveModel.mapDomain_placeMap_corrBar_single_eq_of_frobenius_of_two_mul_dvd`](thm.html#CerednikDrinfeld.ShimuraCurveModel.mapDomain_placeMap_corrBar_single_eq_of_frobenius_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_pt_frobeniusTwist_eq_specMap_frobenius_comp_pt.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_CerednikDrinfeld_QMModuliWitnessD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM IsDedekindDomain
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.pt_frobeniusTwist_eq_specMap_frobenius_comp_pt
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {M : ShimuraCurveModel R ι 𝒮} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' D : ℕ}
    (w : M.ModuliWitnessD Λ N q q' D)
    (k : Type) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (sk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (Ā Āℓ : FakeEllipticCurve Λ N k) (hFV : FakeEllipticCurve.HasFrobeniusVerschiebung ℓ Ā Āℓ) :
    (w.pt k sk Āℓ).1 = Spec.map (CommRingCat.ofHom (frobenius k ℓ)) ≫ (w.pt k sk Ā).1 := by sorry
