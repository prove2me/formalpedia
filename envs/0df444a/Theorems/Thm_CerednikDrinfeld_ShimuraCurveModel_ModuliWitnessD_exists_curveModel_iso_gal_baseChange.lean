-- Prove2me | Theorems.Thm_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_exists_curveModel_iso_gal_baseChange
-- name    : CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.exists_curveModel_iso_gal_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/713ede96-b825-56b8-9cff-df3731fbcf22
-- title:
--   Galois-equivariant curve model on the geometric generic fibre
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $R_0$ of $\mathbb H[\mathbb Q,a,b]$, a $\mathbb Q$-algebra map $\iota$ from $\mathbb H[\mathbb Q,a,b]$ to $M_2(\mathbb R)$, a family $\mathcal S$ of sets of units of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{\mathrm f}$, and a `ShimuraCurveModel` $M$ for these data (in particular a curve function field $M.F$ over $\mathbb Q$, its geometric companion $M.\mathrm{Fbar}$ over $\overline{\mathbb Q}$ with the embedding $M.\mathrm{toBar}$ generating $M.\mathrm{Fbar}$ and preserving linear independence, and the Galois action $M.\mathrm{gal}$ recorded by $M$). Fix a $\mathbb Z$-submodule $\Lambda$, naturals $N,q,q',D$, and a witness $w : M.\mathrm{ModuliWitnessD}\ \Lambda\ N\ q\ q'\ D$, so $w.X$ is an integral scheme with smooth proper structure morphism $\pi_X$ to $\operatorname{Spec}\mathbb Z[1/D]$, carrying the moduli dictionary for fake elliptic curves with $\Lambda$-action and level-$N$ data and a ring isomorphism $w.eF : M.F \cong$ the function field of $w.X$. Assume $w.\mathrm{IsGoodReductionModel}$: $\pi_X$ is smooth of relative dimension $1$, and for every algebraically closed field $k$ and every morphism $\operatorname{Spec} k \to \operatorname{Spec}\mathbb Z[1/D]$ the pullback of $\pi_X$ is integral. Let $O$ be a commutative ring with ring maps $j : \mathbb Z[1/D] \to O$ and $i : O \to \overline{\mathbb Q}$. Then there exist a `CurveModel` $\mathfrak M$ of $M.\mathrm{Fbar}$ over $\overline{\mathbb Q}$ — an integral scheme $\mathfrak M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\overline{\mathbb Q}$, with an isomorphism of $M.\mathrm{Fbar}$ onto its function field over the base and a bijection of its closed points with the places of $M.\mathrm{Fbar}/\overline{\mathbb Q}$ matching stalks with valuation rings — and an isomorphism $e$ from $\mathfrak M.C$ onto $(w.X \times_{\mathbb Z[1/D]} O) \times_O \overline{\mathbb Q}$ such that $e$ followed by the projection to $\operatorname{Spec}\overline{\mathbb Q}$ is $\mathfrak M.\mathrm{toBase}$, and such that for every $\sigma \in \operatorname{Aut}(\overline{\mathbb Q}/\mathbb Q)$ fixing $i(r)$ for all $r \in O$ and all sections $x,y$ of $\mathfrak M.\mathrm{toBase}$: if $y$ followed by $e$ and the first projection to $w.X \times_{\mathbb Z[1/D]} O$ equals $\operatorname{Spec}\sigma$ followed by the same composite for $x$, then $\mathfrak M.\mathrm{pointEquivPlace}(y) = M.\mathrm{gal}(\sigma) \cdot \mathfrak M.\mathrm{pointEquivPlace}(x)$ in the places of $M.\mathrm{Fbar}$.
--
--   This is the passage from a smooth proper integral model of a quaternionic Shimura curve over $\mathbb Z[1/D]$ to a curve model of its geometric function field on the geometric generic fibre, with the point–place dictionary compatible with the Galois action carried by the Shimura-curve model; the ring $O$ and the maps $j,i$ are left arbitrary so that the statement can later be instantiated at a discrete valuation ring inside an inertia field. It feeds the analysis of the inertia action on torsion of the Jacobian, being cited by [`CerednikDrinfeld.ShimuraCurveModel.galJ_eq_self_of_mem_inertiaSubgroupIn_of_moduliWitness_of_two_mul_dvd`](thm.html#CerednikDrinfeld.ShimuraCurveModel.galJ_eq_self_of_mem_inertiaSubgroupIn_of_moduliWitness_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_exists_curveModel_iso_gal_baseChange.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMModuliPropsD
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsDedekindDomain CerednikDrinfeld

theorem CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.exists_curveModel_iso_gal_baseChange
    {a b : ℚ} {R₀ : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (M : ShimuraCurveModel R₀ ι 𝒮) {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' : ℕ} {D : ℕ}
    (w : M.ModuliWitnessD Λ N q q' D) (hgood : w.IsGoodReductionModel)
    (O : Type) [CommRing O] (j : Localization.Away ((D : ℕ) : ℤ) →+* O)
    (i : O →+* AlgebraicClosure ℚ) :
    ∃ (𝔐 : CurveModel (AlgebraicClosure ℚ) M.Fbar)
      (e : 𝔐.C ⟶ pullback (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)))
      (_ : IsIso e),
      e ≫ pullback.snd (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) = 𝔐.toBase ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ r : O, σ (i r) = i r) →
        ∀ x y : {p : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔐.C // p ≫ 𝔐.toBase = 𝟙 _},
          y.1 ≫ e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) =
            Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
              x.1 ≫ e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) →
          𝔐.pointEquivPlace y = M.gal σ • 𝔐.pointEquivPlace x := by sorry
