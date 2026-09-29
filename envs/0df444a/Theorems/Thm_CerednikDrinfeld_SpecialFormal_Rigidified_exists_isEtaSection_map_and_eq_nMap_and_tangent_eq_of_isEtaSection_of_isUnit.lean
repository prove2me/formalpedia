-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/a44b17c2-c98b-5a0e-83af-da26c2d7b868
-- title:
--   Fibre transport of an η-section along g
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring with a ring homomorphism $\iota\colon \mathbb{W}(\mathbb{F}_{p^2})\to O$, and $\Phi$ a formal $\mathcal{O}_D$-module over $O/pO$ whose Cartier module splits as the direct sum of its graded pieces of degrees $0$ and $1$ for $\bar\iota = \iota \bmod p$ (hypothesis `hcΦ`), equipped with an additive rigidification $r_\Phi\colon \mathbb{Z}_p^2 \to N$ of the associated graded Cartier module data. Let $B$ be a $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi\colon O\to B$, and $t = (X,n,\rho)$ a rigidified object over $B$ that is admissible for $(\iota,\psi)$: $X$ is special, of height $4$, and $\rho$ is an isogeny of height $4n$ from $\bar\Phi$ to $\bar X$. Fix $f \in B$ and, for the localisation $B\to B_f$, the three complementarity hypotheses for the gradings of $X_f$, $\bar X_f$ and $\bar\Phi_f$, a canonical $L$-map $L$ on $M = M(X_f)$, an index $i \in \{0,1\}$, an element $z$ of $N(M)$ and $v\in\mathbb{Q}_p^2$ such that $z$ is an $\eta$-section of index $i$ with coordinates $v$: $z$ lies in the $\eta$-piece of $L$ at $i$, and the image under $\eta$-reduction of $\varpi_N^{\,i} z$ stands in the lattice relation, with respect to the rigidification numerology of $t$ and $r_\Phi$, to $p^i v$. Let $g\colon B\to K$ be a ring homomorphism into a $\mathbb{Z}_p$-algebra $K$ compatible with the $\mathbb{Z}_p$-structures, with $p$ nilpotent in $K$ and $g(f)$ a unit, and assume $t\otimes_g K$ is admissible for $(\iota, g\circ\psi)$. Then, over the localisation of $K$ at the powers of $1$, there exist the three complementarity hypotheses, a canonical $L$-map $L'$, an element $z'$ of the corresponding $N$-module, and a proof that $z'$ is an $\eta$-section of $t\otimes_g K$ of the same index $i$ with the same coordinates $v$, such that: first, there is an identification of the formal group of $X_f$ pushed forward along $B_f\to K\to K_1$ (the extension of $g$ given by invertibility of $g(f)$, followed by the localisation map) with that of $(t\otimes_g K)_1$, under which the induced Cartier base-change map commutes with Verschiebung and with $\varpi$, and $z'$ is the image of $z$ under the induced map of $N$-modules; secondly, for every $m\in M$ whose class modulo the image of Verschiebung equals $u(L)$ applied to $z$ (via the first component of its $\eta$-piece membership), there is $m'$ over $K_1$ whose class modulo the image of Verschiebung equals $u(L')$ applied to $z'$ and whose tangent coordinates satisfy $\mathrm{tangent}(m')_k =$ the image of $\mathrm{tangent}(m)_k$ under $B_f \to K \to K_1$ for each $k$.
--
--   This is the base-change functoriality of $\eta$-sections and of the map $u$ in the Cartier-theoretic description of the Čerednik–Drinfeld uniformisation: a presentation of the coordinates $v$ living over a Zariski neighbourhood $D(f)$ is transported to the fibre at a point, the localisation at $f$ becoming invertible there. It is used in the verification of the $N_i$/$u_i$ clauses of the Cartier quadruple, for instance by [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_mem_etaPiece_tangent_eq_of_line_transport`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_mem_etaPiece_tangent_eq_of_line_transport) and in the surjectivity statements for the stalk maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (f : B) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
    (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
    (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (i : Fin 2) (z : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (v : Fin 2 → ℚ_[p])
    (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v)
    {K : Type} [CommRing K] [Algebra ℤ_[p] K] (g : B →+* K)
    (hg : g.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] K) (hK : IsNilpotent (p : K)) (hgf : IsUnit (g f))
    (ht' : (t.map g).IsAdmissible ι (g.comp ψ)) :
    ∃ (hc' : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom (1 : K)))
      (hcb' : (t.map g).IsGradedSbar ι (g.comp ψ) (Rigidified.awayHom (1 : K)))
      (hcΦ' : Rigidified.IsGradedPhiS (Φ := Φ) ι (g.comp ψ) (Rigidified.awayHom (1 : K)))
      (L' : (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').M →+ (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').NMod) (hL' : (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').IsCanonicalLMap L')
      (z' : (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').NMod)
      (hz' : (t.map g).IsEtaSection ι hcΦ rΦ (g.comp ψ) ht'.2.2.1 (Rigidified.awayHom (1 : K)) hc' hcb' hcΦ' L' hL' i z' v),
      (∃ (hXh : (t.XS (Rigidified.awayHom f)).F.map ((algebraMap K (Rigidified.Baway (1 : K))).comp (IsLocalization.Away.lift f (g := g) hgf : Rigidified.Baway f →+* K)) = ((t.map g).XS (Rigidified.awayHom (1 : K))).F)
         (hbcV : ∀ x, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).verschiebung x) =
           (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXh x))
         (hbcPi : ∀ x, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).varpi x) =
           (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXh x)),
         z' = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nMap (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc') (MvFormalGroup.CartierModule.baseChangeEq _ hXh) hbcV hbcPi z) ∧
      ∀ m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M,
        ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ →
        ∃ m' : (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').M,
          (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').vRange.mkQ m' = (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').u L' hL'.isCartierLMap.map_verschiebung ⟨z', (AddSubgroup.mem_inf.mp hz'.1).1⟩ ∧
          ∀ k, MvFormalGroup.CartierModule.tangent m' k =
            algebraMap K (Rigidified.Baway (1 : K))
              ((IsLocalization.Away.lift f (g := g) hgf : Rigidified.Baway f →+* K)
                (MvFormalGroup.CartierModule.tangent m k)) := by sorry
