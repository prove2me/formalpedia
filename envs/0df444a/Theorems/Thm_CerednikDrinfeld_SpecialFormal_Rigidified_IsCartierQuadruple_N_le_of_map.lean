-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_le_of_map
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.N_le_of_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/06f69561-a34b-500f-9d63-317467d14f8d
-- title:
--   Base change of a Cartier quadruple: the lattices can only grow
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring and $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$ a ring homomorphism, and let $\Phi$ be a formal $O_D$-module over $O/pO$. Assume: $\Phi$ is special for the reduced structure map `Rigidified.jbar ι` (its Lie algebra is the direct sum of the complementary invertible pieces `lieZero`, `lieOne`); $\Phi$ has height $4$, i.e. the kernel of its $p$-multiplication series has degree $p^4$; the degree-$0$ and degree-$1$ Teichmüller eigenpieces of the Cartier module of $\Phi$ are complementary (`hcΦ`); and $r_\Phi : (\mathbb{Z}_p)^2 \to$ `NMod` of the graded Cartier module data of $\Phi$ is an additive map which, for every canonical $L$-map $L$ on that data, maps $(\mathbb{Z}_p)^2$ bijectively onto the degree-$0$ piece `etaPiece L _ 0`. Let $B$, $B'$ be noetherian commutative $\mathbb{Z}_p$-algebras in which $p$ is nilpotent, $\psi : O \to B$, $\psi' : O \to B'$ ring homomorphisms, and $f : B \to B'$ a $\mathbb{Z}_p$-algebra map with $f \circ \psi = \psi'$. Let $t = (X, n, \rho)$ be a rigidified object over $B$ which is admissible for $(\iota, \psi)$, and let $Q$, $Q'$ be Drinfeld data over $B$, $B'$ for $\pi = p \in \mathbb{Z}_p$ and $K = \mathbb{Q}_p$ (full $\mathbb{Z}_p$-lattices $N_0(x) \le N_1(x)$ in $\mathbb{Q}_p^2$ with $pN_1(x) \subseteq N_0(x)$, invertible modules $T_0$, $T_1$ with maps $\Pi_0$, $\Pi_1$, and comparison maps $u_0$, $u_1$). Assume $t$ together with $Q$ satisfies `IsCartierQuadruple` for $(\iota, h_{c\Phi}, r_\Phi, \psi)$, and that the base change `t.map f` together with $Q'$ satisfies it for $\psi'$. Then for every prime $x'$ of $B'$, writing $x =$ `DrinfeldDatum.pointUnder f x'` for the contraction of $x'$ along $f$, one has $Q.N_0(x) \le Q'.N_0(x')$ and $Q.N_1(x) \le Q'.N_1(x')$.
--
--   This is the half of the naturality (base-change) statement for Cartier quadruples asserting that the lattices attached by a Cartier quadruple grow under base change: an $\eta$-section presenting $v$ over a localisation $B_g$ transports to one over $B'_{f(g)}$. It feeds into [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChangeAlong`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChangeAlong), in the comparison between rigidified special formal $O_D$-modules and Drinfeld data underlying the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_le_of_map.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.N_le_of_map
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    {B' : Type} [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[p] B'] (ψ' : O →+* B')
    (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B') (hf : (f : B →+* B').comp ψ = ψ')
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q)
    (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (hQ' : (t.map (f : B →+* B')).IsCartierQuadruple ι hcΦ rΦ ψ' Q') (x' : PrimeSpectrum B') :
    Q.N₀ (DrinfeldDatum.pointUnder f x') ≤ Q'.N₀ x' ∧ Q.N₁ (DrinfeldDatum.pointUnder f x') ≤ Q'.N₁ x' := by sorry
