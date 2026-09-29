-- Prove2me | Theorems.Thm_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_pointEquivPlace_eq_gal_smul_of_ringEquiv_functionField
-- name    : CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.pointEquivPlace_eq_gal_smul_of_ringEquiv_functionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/d81564da-27e9-5ba7-aa2d-396924474e9a
-- title:
--   Galois equivariance of the point–place dictionary after base change
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $R_0$ of $\mathbb{H}[\mathbb{Q},a,b]$, an $\mathbb{Q}$-algebra map $\iota$ of that quaternion algebra into $M_2(\mathbb{R})$, a family $\mathcal{S}$ of sets of units of the finite-adelic quaternion algebra, and a datum $M : \text{ShimuraCurveModel}\ R_0\ \iota\ \mathcal{S}$ (which packages fields $M.F$, $M.\overline{F}$, $M.F_{\mathbb C}$ that are curves over $\mathbb{Q}$, $\overline{\mathbb{Q}}$, $\mathbb{C}$, the map `M.toBar` from $M.F$ to $M.\overline{F}$, and the further data of that structure, among them `M.gal`). Let $\Lambda$, $N$, $q$, $q'$, $D$ be natural numbers and $w : M.\text{ModuliWitnessD}\ \Lambda\ N\ q\ q'\ D$, so that $w.X$ is an integral scheme with a smooth proper morphism $\pi_X$ to $\operatorname{Spec}\mathbb{Z}[1/D]$, equipped with an isomorphism $w.eF$ from $M.F$ onto the function field of $w.X$ and the remaining moduli data. Let $O$ be a commutative ring, $j : \mathbb{Z}[1/D] \to O$ and $i : O \to \overline{\mathbb{Q}}$ ring homomorphisms, and $s : \operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Z}[1/D]$ the morphism with $\operatorname{Spec} i$ followed by $\operatorname{Spec} j$ equal to $s$; assume $w.X$ and the pullback $w.X \times_{\mathbb{Z}[1/D]} \overline{\mathbb{Q}}$ of $\pi_X$ along $s$ are integral. Assume given a ring isomorphism $e_{\overline F}$ from $M.\overline{F}$ onto the function field of that pullback which (i) carries constants $z \in \overline{\mathbb{Q}}$ to their images under the germ-at-the-generic-point map `baseToFunctionField` of the second projection, and (ii) for every open $U \subseteq w.X$ with $U$ and its preimage under the first projection nonempty and every $t \in \Gamma(w.X,U)$, satisfies $e_{\overline F}(\mathrm{toBar}(w.eF^{-1}(\text{germ of } t))) =$ the germ in the function field of the pullback of the pullback of $t$ along the first projection. Assume further given a curve model $\mathfrak{M} : \text{CurveModel}\ \overline{\mathbb{Q}}\ M.\overline{F}$ (an integral scheme $\mathfrak{M}.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\overline{\mathbb{Q}}$, with a function-field identification $\mathfrak{M}.\text{ffEquiv}$ of $M.\overline{F}$ compatible with constants and a bijection from closed points to places of $M.\overline{F}$ matching stalks with valuation subrings), an isomorphism $e$ from $\mathfrak{M}.C$ onto $(w.X \times_{\mathbb{Z}[1/D]} O) \times_O \overline{\mathbb{Q}}$ whose composition with the second projection is $\mathfrak{M}.\text{toBase}$, and the compatibility that for every such $U$ and $t$ the element $\mathfrak{M}.\text{ffEquiv}^{-1}$ of the germ of the pullback of $t$ along $e$ followed by the two first projections onto $w.X$ agrees with $e_{\overline F}^{-1}$ of the corresponding germ on $w.X \times_{\mathbb{Z}[1/D]} \overline{\mathbb{Q}}$. The conclusion: for every $\sigma \in \operatorname{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing $i(r)$ for all $r \in O$, and for all $\overline{\mathbb{Q}}$-points $x,y$ of $\mathfrak{M}$ (sections of $\mathfrak{M}.\text{toBase}$), if the composite of $y$ with $e$ and the first projection equals $\operatorname{Spec}\sigma$ followed by the same composite for $x$, then $\mathfrak{M}.\text{pointEquivPlace}\ y = M.\text{gal}\ \sigma \bullet \mathfrak{M}.\text{pointEquivPlace}\ x$, where $\bullet$ is the action of `M.gal σ` on places of $M.\overline{F}$ over $\overline{\mathbb{Q}}$.
--
--   This is the Galois-equivariance clause of the dictionary between $\overline{\mathbb{Q}}$-points of the base-changed integral model of the Shimura curve and places of its function field: twisting a point by $\sigma$ on the geometric side corresponds to applying the semilinear automorphism $M.\mathrm{gal}\,\sigma$ on the function-field side. It is used in the construction of a curve model compatible with the Galois action and base change ([`CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.exists_curveModel_iso_gal_baseChange`](thm.html#CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.exists_curveModel_iso_gal_baseChange)), and relies on the general transfer of a semilinear automorphism from a base-changing isomorphism of a curve model to its point–place bijection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_pointEquivPlace_eq_gal_smul_of_ringEquiv_functionField.lean

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

theorem CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.pointEquivPlace_eq_gal_smul_of_ringEquiv_functionField
    {a b : ℚ} {R₀ : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (M : ShimuraCurveModel R₀ ι 𝒮) {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' : ℕ} {D : ℕ}
    (w : M.ModuliWitnessD Λ N q q' D)
    (O : Type) [CommRing O] (j : Localization.Away ((D : ℕ) : ℤ) →+* O)
    (i : O →+* AlgebraicClosure ℚ)
    (s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (hs : Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j) = s)
    [AlgebraicGeometry.IsIntegral ↑w.X] [AlgebraicGeometry.IsIntegral ↑(pullback w.πX s)]

    (eFbar : M.Fbar ≃+* ↥((pullback w.πX s).functionField))
    (heFbar_const : ∀ z : AlgebraicClosure ℚ, eFbar (algebraMap (AlgebraicClosure ℚ) M.Fbar z) =
      baseToFunctionField (pullback.snd w.πX s) z)
    (heFbar_germ : ∀ (U : w.X.Opens) [Nonempty (Scheme.Opens.toScheme U)]
      [Nonempty (Scheme.Opens.toScheme ((pullback.fst w.πX s) ⁻¹ᵁ U))] (t : Γ(w.X, U)),
      eFbar (M.toBar (w.eF.symm (w.X.germToFunctionField U t))) =
        (pullback w.πX s).germToFunctionField ((pullback.fst w.πX s) ⁻¹ᵁ U) (((pullback.fst w.πX s).app U).hom t))

    (𝔐 : CurveModel (AlgebraicClosure ℚ) M.Fbar)
    (e : 𝔐.C ⟶ pullback (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i))) [IsIso e]
    (he : e ≫ pullback.snd (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) = 𝔐.toBase)
    (hcm : ∀ (U : w.X.Opens) [Nonempty (Scheme.Opens.toScheme U)]
      [Nonempty (Scheme.Opens.toScheme ((pullback.fst w.πX s) ⁻¹ᵁ U))]
      [Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫ pullback.fst w.πX (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U))]
      (t : Γ(w.X, U)),
      𝔐.ffEquiv.symm (𝔐.C.germToFunctionField ((e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫ pullback.fst w.πX (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U) (((e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫ pullback.fst w.πX (Spec.map (CommRingCat.ofHom j))).app U).hom t)) =
        eFbar.symm ((pullback w.πX s).germToFunctionField ((pullback.fst w.πX s) ⁻¹ᵁ U) (((pullback.fst w.πX s).app U).hom t))) :
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ r : O, σ (i r) = i r) →
      ∀ x y : {p : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔐.C // p ≫ 𝔐.toBase = 𝟙 _},
        y.1 ≫ e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) →
        𝔐.pointEquivPlace y = M.gal σ • 𝔐.pointEquivPlace x := by sorry
