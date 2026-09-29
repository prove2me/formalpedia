-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/f2d66abf-22e5-56de-9a1a-a2e7caec47b4
-- title:
--   The degree-0 η-stalk contains pᵃℤₚ²
-- statement:
--   Fix a prime $p$, a commutative ring $O$ and a ring homomorphism $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$, and let $\Phi$ be a formal $O_D$-module of dimension $2$ over $O/pO$ (a commutative $2$-dimensional formal group law with an action of $\mathbb{W}(\mathbb{F}_{p^2})$ and a uniformiser endomorphism $\varpi$ with $\varpi^2 = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$). It is assumed that $\Phi$ is special for `Rigidified.jbar ι`, the reduction of $\iota$ modulo $p$ — its Lie algebra is the direct sum of the eigenspaces `lieZero` and `lieOne`, both invertible modules — that the kernel of $[p]$ on $\Phi$ has degree $p^4$, and that the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ (the eigenspaces for the Teichmüller homotheties, with eigenvalues $j(c)$ and $j(c)^p$) are complementary, via `hcΦ`; write $D_\Phi$ for the resulting graded Cartier module datum and $N_\Phi$ for its associated $N$-module. Further data: an additive map $r_\Phi : \mathbb{Z}_p^2 \to N_\Phi$, the existence of a canonical $L$-map for $D_\Phi$, and the hypothesis that for every canonical $L$-map $L$ on $D_\Phi$ the map $r_\Phi$ is a bijection from all of $\mathbb{Z}_p^2$ onto the degree-$0$ $\eta$-piece `etaPiece L _ 0`. Finally let $B$ be a Noetherian commutative $\mathbb{Z}_p$-algebra, $\psi : O \to B$ a ring homomorphism, $p$ nilpotent in $B$, and $t = (X, n, \rho)$ a rigidified object over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for $\psi \circ \iota$, the kernel of $[p]$ on $X$ has degree $p^4$, and $\rho$ is an isogeny of height $4n$ from $\Phi \otimes_{O} B/pB$ to $X \bmod p$. The conclusion is that for every point $x \in \operatorname{Spec} B$ there is $a \in \mathbb{N}$ such that for every $w \in \mathbb{Z}_p^2$ one can find $f \notin x$, together with the three complementarity hypotheses over the localisation $B_f$ (for the Cartier module of $X_f$, of its reduction $\bar X_f$, and of the base change of $\Phi$), a canonical $L$-map $L$ for the datum of $X_f$, and an element $z$ of the corresponding $N$-module, such that `t.IsEtaSection … 0 z ((p : ℚ_[p]) ^ a • w)` holds: $z$ lies in the degree-$0$ $\eta$-piece of $L$, and the lattice relation holds between the image of $z$ under the reduction map `etaRed` and the vector $p^a w$, namely there are $m, k \in \mathbb{N}$ and $w' \in \mathbb{Z}_p^2$ with $p^m \cdot (p^a w) = w'$ in $\mathbb{Q}_p^2$ and $p^k \cdot (\text{rigidNum})(w') = p^{k + n + m} \cdot \mathrm{etaRed}(z)$.
--
--   This is the surjectivity half of the comparison, in the Čerednik–Drinfeld setting, between the $\mathbb{Z}_p^2$ of periods of the special formal module $\Phi$ and the $\eta$-sections of a rigidified admissible deformation: locally at each point of $\operatorname{Spec} B$, all integral vectors divisible by a fixed power of $p$ are presented in degree $0$. It feeds the statements that the set of vectors so presented is a submodule and that this submodule is a full lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    ∀ x : PrimeSpectrum B, ∃ a : ℕ, ∀ w : Fin 2 → ℤ_[p],
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z ((p : ℚ_[p]) ^ a • fun j => ((w j : ℤ_[p]) : ℚ_[p])) := by sorry
