-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_omegaPackage_padic_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing
-- name    : CerednikDrinfeld.FormalOmega.omegaPackage_padic_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/a6504a14-e517-5784-b4c3-6ec9d73eac87
-- title:
--   Fibre-square gluing for the p-adic Ω̂ package, Noetherian case
-- statement:
--   Fix a prime $p$, an element $\pi\in\mathbb{Z}_p$, a commutative ring $O$ and a ring homomorphism $c\colon\mathbb{Z}_p\to O$, and write $\mathcal{F}$ for the moduli package `omegaPackage p π c` over $O$, obtained from the functor `Omega` for the coefficient pair $(\mathbb{Z}_p,\mathbb{Q}_p)$ and the parameter $\pi$ by transport along $c$; thus $\mathcal{F}$ assigns a type $\mathcal{F}(B,\psi)$ to each commutative ring $B$ with a ring map $\psi\colon O\to B$ and $p$ nilpotent in $B$, together with functorial transition maps along structure-compatible ring homomorphisms. The assertion is the following property of $\mathcal{F}$. Let $B,B',B''$ be Noetherian commutative rings with structure maps $\psi\colon O\to B$, $\psi'\colon O\to B'$, $\psi''\colon O\to B''$ and $p$ nilpotent in each, and let $\varphi'\colon B'\to B$, $\varphi''\colon B''\to B$ be ring homomorphisms with $\varphi'\circ\psi'=\psi$ and $\varphi''\circ\psi''=\psi$, both surjective and with nilpotent kernel ideals. Let $P=\{(b',b'')\in B'\times B'' : \varphi'(b')=\varphi''(b'')\}$ be the fibre-product subring, equipped with the structure map $o\mapsto(\psi'(o),\psi''(o))$, and assume $p$ is nilpotent in $P$. Then for all $x'\in\mathcal{F}(B',\psi')$ and $x''\in\mathcal{F}(B'',\psi'')$ having the same image in $\mathcal{F}(B,\psi)$ under $\varphi'$ and $\varphi''$, there is a unique $z\in\mathcal{F}(P)$ whose images under the two projections $P\to B'$ and $P\to B''$ are $x'$ and $x''$.
--
--   This is the exactness (Milnor patching) property of Drinfeld's $p$-adic formal upper half-plane moduli package on fibre squares coming from surjections with nilpotent kernel, here in the corner where the three rings are Noetherian: objects over $B'$ and $B''$ agreeing over $B$ glue uniquely over the fibre product. It supplies the gluing input for [`CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_isNoetherianRing_of_lieVarpi_eq_zero`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_isNoetherianRing_of_lieVarpi_eq_zero), the bijectivity of the period map on Noetherian bases in the Čerednik–Drinfeld comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_omegaPackage_padic_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_OmegaModuliPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.omegaPackage_padic_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing
    (p : ℕ) [Fact p.Prime] (π : ℤ_[p]) {O : Type} [CommRing O] (c : ℤ_[p] →+* O)
    :
    (∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (_hs' : Function.Surjective φ') (_hs'' : Function.Surjective φ'')
    (_hn' : IsNilpotent (RingHom.ker φ')) (_hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))
    (x' : (omegaPackage (K := ℚ_[p]) p π c).obj B' ψ' hB') (x'' : (omegaPackage (K := ℚ_[p]) p π c).obj B'' ψ'' hB''),
      (omegaPackage (K := ℚ_[p]) p π c).map hB' hB φ' hφ' x' = (omegaPackage (K := ℚ_[p]) p π c).map hB'' hB φ'' hφ'' x'' →
      ∃! z : (omegaPackage (K := ℚ_[p]) p π c).obj (ModuliPackage.pullbackRing φ' φ'')
          (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
        (omegaPackage (K := ℚ_[p]) p π c).map hP hB' (ModuliPackage.pullbackFst φ' φ'')
            (ModuliPackage.pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
        (omegaPackage (K := ℚ_[p]) p π c).map hP hB'' (ModuliPackage.pullbackSnd φ' φ'')
            (ModuliPackage.pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'') := by sorry
