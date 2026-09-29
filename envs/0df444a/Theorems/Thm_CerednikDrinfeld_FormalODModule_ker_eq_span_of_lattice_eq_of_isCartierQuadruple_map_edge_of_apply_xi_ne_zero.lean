-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_ne_zero
-- name    : CerednikDrinfeld.FormalODModule.ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/9ace9808-1526-5d82-83fb-6ad72b8339b1
-- title:
--   Kernels of u₀ and u₁ at a ξ-point
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$ (the source `Zp2 p` being $W(\mathbb F_{p^2})$), and write $\bar\jmath$ for the composite of $\iota$ with the quotient map $W(k)\to W(k)/pW(k)$.
--
--   **Data and hypotheses on $\Phi$.** $\Phi$ is a formal $\mathcal O_D$-module of dimension $2$ over $W(k)/pW(k)$, i.e. a commutative formal group law `Φ.F` in two variables equipped with an action of $W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$. The hypothesis `hΦ` says that $\Phi$ is special for $\bar\jmath$: the weight-$0$ and weight-$1$ parts $\mathrm{Lie}_0$, $\mathrm{Lie}_1$ of the tangent space are complementary and each invertible as a module over $W(k)/pW(k)$; `hΦ4` says that the kernel of $[p]$ on $\Phi$ is finite projective of degree $p^4$ (rank $p^4$ after any base change to a field); `h0Φ` says that $\mathrm{Lie}_0$ is annihilated by the linear part of $\varpi$; `hcΦ` says that the graded pieces of index $0$ and $1$ of the Cartier module $C(\Phi)$ — the subgroups on which $[\,\omega(c)\,]$ acts as the homothety by $\bar\jmath(\omega(c))^{p^n}$ for all $c\in\mathbb F_{p^2}$, $n=0,1$ — are complementary, so that `Φ.toGradedCartierModuleData` assembles $C(\Phi)$ into graded Cartier module data $D_\Phi$ with Frobenius, (integral) Verschiebung, $\varpi$ and the two pieces. Further, $r_\Phi\colon \mathbb Z_p^2\to D_\Phi.\mathrm{NMod}$ is an additive map, and `hrΦ` requires that for every canonical $L$-map $L$ on $D_\Phi$ the map $r_\Phi$ is a bijection of $\mathbb Z_p^2$ onto the index-$0$ $\eta$-piece of $L$.
--
--   **The element $g$.** $g\in\mathrm{GL}_2(\mathbb Q_p)$ with `hg` asserting that its matrix is $\mathrm{diag}(p,1)$.
--
--   **Data over the edge ring.** $E:=$ `EdgeFamily.edgeRingCharP p (W(k)/pW(k))` is the localisation of the edge chart ring over $W(k)/pW(k)$ away from the discriminant, with distinguished elements $\xi,\eta$. $X$ is a formal $\mathcal O_D$-module over $E$ and $\gamma_0,\gamma_1\in C(X)$; with respect to the structure map $W(\mathbb F_{p^2})\to E$ obtained from $\iota$ by reduction and the structural algebra map, `hγ` says that $\gamma_i$ lies in the graded piece of index $i$ and that the matrix of tangent vectors of $\gamma_0,\gamma_1$ has unit determinant, `hγa` says that $\gamma$ has the edge structure constants `EdgeFamily.edgeRingConstants p (W(k)/pW(k))` (built from $\xi$ and $\eta$), `hXs` says that $X$ is special and `hX4` that $X$ has height $4$.
--
--   **The specialisation $f_0$ and the isogeny $\rho_0$.** $f_0\colon E\to W(k)/pW(k)$ is a ring homomorphism splitting the structural algebra map (`hf₀`) and killing $\xi$ (`hf₀ξ`) and $\eta$ (`hf₀η`). For $m\in\mathbb N$ and $\rho_0$ a $2$-tuple of power series over $W(k)/pW(k)$, `hρ₀` says that $\rho_0$ is an isogeny $\Phi\to X\otimes_{f_0}W(k)/pW(k)$ of height $4m$ (an $\mathcal O_D$-homomorphism whose kernel has degree $p^{4m}$). Write $t_0$ for the rigidified datum `Rigidified.mk (X.map f₀) m` with the reduction of $\rho_0$ modulo the $p$-ideal; `hOD₀` says that its structural series is an $\mathcal O_D$-homomorphism from $\bar\Phi$ to $\bar X$, `hcb` and `hcΦg` are the complementarity statements (`IsGradedSbar`, `IsGradedPhiS`) for the graded pieces of $t_0$ and of $\bar\Phi$ after base change along the identity of $W(k)/pW(k)$. Finally, for $a\in\mathbb N$, the hypothesis `hN` pins down the rigidifying numeration `rigidNum` — the composite of $r_\Phi$ with the maps on $N$-modules induced by base change along $f_0$-type maps and by $\rho_0$ — on the standard basis: for each $i$, $p^a$ times its value at $\mathrm{e}_i$ equals $p^{a+m}$ times the $i$-th entry of the pair consisting of $\mathrm{nMk}(\bar\gamma_0,0)$ and $\mathrm{nVarpi}(\mathrm{nMk}(\bar\gamma_1,0))$, where $\bar\gamma_i$ denotes the image of $\gamma_i$ under the successive Cartier-module base changes along $f_0$, the quotient by the $p$-ideal and the identity.
--
--   **The isogeny $\rho_1$.** $\rho_1$ is a homomorphism of formal $\mathcal O_D$-modules from $(X\otimes_{f_0}W(k)/pW(k))\otimes E$ to $X$ whose action on Cartier modules sends the base change of $\gamma_0$ to $p\gamma_0-V(\omega(\eta^{p^2})\gamma_1)$ (`hρ₁0`) and the base change of $\gamma_1$ to $p\gamma_1-V(\omega(\xi^{p^2})\gamma_0)$ (`hρ₁1`), $\omega$ denoting the Teichmüller lift and $V$ the integral Verschiebung; `hρ₁h` says that $\rho_1$ is an isogeny of height $4$.
--
--   **The point and the quadruple.** $\Omega$ is an algebraically closed field which is a $\mathbb Z_p$-algebra, $y\colon E\to\Omega$ a ring homomorphism with $y(\xi)\neq 0$ (`hyξ`), and $Q$ a Drinfeld datum over $\Omega$ for the uniformiser $p$ of $\mathbb Z_p\subset\mathbb Q_p$: a pair of full $\mathbb Z_p$-lattices $N_0(x)\le N_1(x)$ in $\mathbb Q_p^2$ depending on $x\in\operatorname{Spec}\Omega$ with $pN_1\subseteq N_0$ and the requisite openness, two invertible $\Omega$-modules $T_0,T_1$ with maps $\Pi_0,\Pi_1$ composing to multiplication by $p$, and stalkwise $\Omega_x$-linear maps $u_i(x)\colon \Omega_x\otimes_{\mathbb Z_p}N_i(x)\to (T_i)_x$ compatible with the inclusion and with multiplication by $p$. The hypothesis `hQ` says that the rigidified datum `Rigidified.mk X (m+1)` with structural series the composite of the reductions of $\rho_1$ and $\rho_0$, base changed along $y$, is a Cartier quadruple with respect to $\iota$, `hcΦ`, $r_\Phi$, the structure map $y\circ(\text{algebra map})\circ(\text{quotient})$ and $Q$: that is, its structural series is an $\mathcal O_D$-homomorphism, there are identifications of $T_0,T_1$ with the two graded parts of the tangent space of $X$ intertwining $\Pi_0,\Pi_1$ with the linear part of $\varpi$, and at each prime the lattices $N_0,N_1$ consist exactly of the vectors presented by $\eta$-sections of indices $0$ and $1$, the germs of $u_0,u_1$ being computed from those sections.
--
--   Finally $x\in\operatorname{Spec}\Omega$, and the two lattices at $x$ are prescribed: `h₀` says $N_0(x)=\mathbb Z_p^2$ is the standard full lattice, and `h₁` says $N_1(x)$ is the image of the standard lattice under the scalar matrix $u^{-1}$, where $u$ is the unit of $\mathbb Q_p$ given by $p$; thus $N_1(x)=p^{-1}\mathbb Z_p^2$.
--
--   **Conclusion.** Both kernels are free of rank one, cut out by the vector $y(\xi)e_0+e_1$:
--
--   (i) $\ker\bigl(u_0(x)\bigr)$ is the $\Omega_x$-span of the single element obtained by transporting, along the equality of lattices given by `h₀` read from right to left, the element $\,y(\xi)\otimes e_0+1\otimes e_1\,$ of $\Omega_x\otimes_{\mathbb Z_p}\mathbb Z_p^2$, where $e_0,e_1$ are the standard basis vectors of the standard lattice and $y(\xi)$ is taken in $\Omega_x$ via the localisation map;
--
--   (ii) $\ker\bigl(u_1(x)\bigr)$ is the $\Omega_x$-span of the single element obtained from the same element $y(\xi)\otimes e_0+1\otimes e_1$ by applying the base-changed isomorphism $\Omega_x\otimes\mathbb Z_p^2\to\Omega_x\otimes p^{-1}\mathbb Z_p^2$ induced by the scalar matrix $u^{-1}$, and then transporting along the equality of lattices given by `h₁` read from right to left.
--
--   This is the kernel half of the identification, at a point of the edge family where $y(\xi)\neq 0$, of the Drinfeld datum attached to a Cartier quadruple with the datum coming from the two standard lattices $\mathbb Z_p^2\subset p^{-1}\mathbb Z_p^2$: the two stalk maps $u_0,u_1$ have as kernels the lines spanned by $y(\xi)e_0+e_1$ and its multiple by $p^{-1}$. It is used by [`CerednikDrinfeld.FormalODModule.exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_ne_zero`](thm.html#CerednikDrinfeld.FormalODModule.exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_ne_zero), which produces from the edge family a Cartier quadruple whose lines match a prescribed Deligne datum, and it rests on the existence of $\eta$-sections of indices $0$ and $1$ with the expected tangent vectors together with the two spanning lemmas for $\ker u_0$ and $\ker u_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_ne_zero.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_ne_zero
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
(hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
(X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F)
(hγ : X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ)
(hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hXs : X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (hX4 : X.HasHeight 4)

(f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ : f₀.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0)
(m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m))
(hOD₀ : FormalODModule.IsODHom (Rigidified.Φbar (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.Xbar (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.ρ (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))))
(hcb : Rigidified.IsGradedSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(a : ℕ)
(hN : ∀ i : Fin 2,
    p ^ a • (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg) (Pi.single i 1) =
      p ^ (a + m) • (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0),
          ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] i))
(ρ₁ : FormalODModule.Hom ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X)
(hρ₁0 : CartierModule.map ρ₁.toLawHom (baseChange (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0))) =
    (p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 0 -
      verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 1))
(hρ₁1 : CartierModule.map ρ₁.toLawHom (baseChange (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1))) =
    (p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1 -
      verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0))
(hρ₁h : FormalODModule.IsIsogenyOfHeight ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X ρ₁.toSeries 4)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] (y : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* Ω)
    (hyξ : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ≠ 0)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω)
    (hQ : ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsCartierQuadruple ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) Q)
    (x : PrimeSpectrum Ω)
    (h₀ : Q.N₀ x = (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1)
    (h₁ : Q.N₁ x = (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p])).1) :
        LinearMap.ker (Q.u₀ x) = Submodule.span (locRing Ω x)
          {transportEquiv (locRing Ω x) (M₁ := stdFullLattice ℚ_[p]) (M₂ := Q.L₀ x) h₀.symm
            (algebraMap Ω (locRing Ω x) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : locRing Ω x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)} ∧
        LinearMap.ker (Q.u₁ x) = Submodule.span (locRing Ω x)
          {transportEquiv (locRing Ω x)
              (M₁ := FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
                (stdFullLattice ℚ_[p])) (M₂ := Q.L₁ x) h₁.symm
            (actBaseChange (locRing Ω x) (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
              (stdFullLattice ℚ_[p])
              (algebraMap Ω (locRing Ω x) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : locRing Ω x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1))} := by sorry
