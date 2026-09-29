-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_baseChange_comparison
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_baseChange_comparison
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/c99279fa-7420-5ed2-9119-560384cace2e
-- title:
--   Base change comparison of graded Cartier data for rigidified triples
-- statement:
--   Fix a prime $p$ and write $\mathbb{Z}_{p^2}$ for the Witt vectors of $\mathbb{F}_{p^2}$. Let $O$ be a commutative ring with a ring homomorphism $\iota:\mathbb{Z}_{p^2}\to O$, and let $\Phi$ be a formal $O_D$-module of dimension $2$ over $O/pO$ such that the graded pieces in degrees $0$ and $1$ of its Cartier module, taken with respect to $\bar\jmath=\iota$ followed by reduction mod $p$, are complementary submodules (hypothesis `hcΦ`); fix an additive map $r_\Phi$ from $\mathbb{Z}_p^2$ to the $N$-module of the graded Cartier data of $\Phi$. Let $\psi:O\to B$, $\psi':O\to B'$ and $f:B\to B'$ be ring homomorphisms with $\psi'=f\circ\psi$, and let $t$ be a rigidified triple over $B$ (a formal $O_D$-module $t.X$ over $B$, an integer $t.n$, and a system of power series $t.\rho$ over $B/pB$) such that $t.\rho$ is a homomorphism of formal $O_D$-modules from `t.Φbar ψ` to $t.\overline{X}$, and likewise for the base change $t.\mathrm{map}\,f$ over $B'$ with $\psi'$. Let further $g:B\to S$, $g':B'\to S'$ and $e:S\to S'$ satisfy $g'\circ f=e\circ g$, and assume, both for $(t,\psi,g)$ and for $(t.\mathrm{map}\,f,\psi',g')$, that degrees $0$ and $1$ are complementary in the Cartier modules of $X_S$, of $\overline{X}_S$ and of the corresponding base change of $\Phi$. Finally let $\gamma:\mathrm{Fin}\,2\to$ (Cartier module of $X_S$) be homogeneous with $\gamma_i$ in the piece of degree $i$ and with invertible determinant of the matrix of tangent coordinates. The conclusion asserts the existence of an additive map $bc$ from the Cartier module of $X_S$ to that of $(t.\mathrm{map}\,f)_{S'}$ which is a base change along $e$ of the associated graded Cartier data, i.e. it is semilinear for $W(e)$, commutes with Frobenius, Verschiebung and $\varpi$, preserves the graded pieces, and carries some homogeneous $V$-basis to a homogeneous $V$-basis; such that on tangent coordinates $\mathrm{tangent}(bc\,m)_i=e(\mathrm{tangent}(m)_i)$ for all $m$ and all $i$; and such that there is an additive map $\overline{bc}$ between the $N$-modules of the reduced graded data of $\overline{X}_S$ and of $(t.\mathrm{map}\,f)\overline{{}_{S'}}$ which intertwines the reduction maps `etaRed` with the map induced on $N$-modules by $bc$, and which intertwines the rigidification numerator maps `rigidNum` built from $\iota$, `hcΦ` and $r_\Phi$.
--
--   This is the functoriality statement for the graded Cartier data attached to a rigidified formal $O_D$-module along a commuting square of base changes, in the Cartier-theoretic description of the Čerednik–Drinfeld uniformisation. It rests on the base-change statement for the graded Cartier data of a formal $O_D$-module, and is used in establishing that the Cartier quadruple data transforms correctly under base change and that the rigidification lattice is respected by maps of rigidified triples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_baseChange_comparison.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_baseChange_comparison
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B') (f : B →+* B') (hf : f.comp ψ = ψ')
    (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (hOD' : FormalODModule.IsODHom ((t.map f).Φbar ψ') (t.map f).Xbar (t.map f).ρ)
    {S S' : Type} [CommRing S] [CommRing S'] (g : B →+* S) (g' : B' →+* S') (e : S →+* S')
    (hge : g'.comp f = e.comp g)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (hc' : (t.map f).IsGradedS ι ψ' g') (hcb' : (t.map f).IsGradedSbar ι ψ' g')
    (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' g')
    (γ : Fin 2 → MvFormalGroup.CartierModule p (t.XS g).F) (hγ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) γ) :
    ∃ (bc : MvFormalGroup.CartierModule p (t.XS g).F →+ MvFormalGroup.CartierModule p ((t.map f).XS g').F)
      (hbc : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' e ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc),
      (∀ (m : MvFormalGroup.CartierModule p (t.XS g).F) (i : Fin 2),
          MvFormalGroup.CartierModule.tangent (bc m) i = e (MvFormalGroup.CartierModule.tangent m i)) ∧
      ∃ bcbar : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod →+ (((t.map (f : B →+* B')).XbarS g').toGradedCartierModuleData (Rigidified.jSbar ι ψ' g') hcb').NMod,
        (∀ z, (t.map f).etaRed ι ψ' g' hc' hcb' (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 z) =
            bcbar (t.etaRed ι ψ g hc hcb z)) ∧
        (∀ w, (t.map f).rigidNum ι hcΦ rΦ ψ' hOD' g' hcb' hcΦg' w = bcbar (t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg w)) := by sorry
