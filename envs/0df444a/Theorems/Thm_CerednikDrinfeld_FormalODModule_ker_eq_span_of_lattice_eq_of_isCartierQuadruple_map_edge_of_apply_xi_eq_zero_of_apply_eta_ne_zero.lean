-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_eq_zero_of_apply_eta_ne_zero
-- name    : CerednikDrinfeld.FormalODModule.ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_eq_zero_of_apply_eta_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/673e5446-edae-5537-9079-6535e2524c04
-- title:
--   Stalk kernels at an η-branch point of the edge family
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, and a ring homomorphism $\iota \colon \mathbb{W}(\mathbb{F}_{p^2}) \to \mathbb{W}(k)$ (here `Zp2 p` is $\mathbb{W}(\mathbb{F}_{p^2})$). Write $O = \mathbb{W}(k)$, $\bar O = O/pO$, and $\bar\iota$ for the composite of $\iota$ with the quotient map $O \to \bar O$. Let $E =$ `EdgeFamily.edgeRingCharP p` $\bar O$ be the edge chart ring over $\bar O$, with its two distinguished elements $\xi$ and $\eta$.
--
--   *Hypotheses on the special formal module $\Phi$ over $\bar O$.* $\Phi$ is a formal $O_D$-module of dimension $2$ over $\bar O$ (a commutative formal group law in two variables with an action of $\mathbb{W}(\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ with $\varpi^2 = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$). The hypothesis `hΦ` says that $\Phi$ is special for $\bar\iota$: the two eigen-submodules `lieZero` and `lieOne` of the tangent space are complementary and each is an invertible $\bar O$-module. The hypothesis `hΦ4` says that $\Phi$ has height $4$, i.e. the kernel algebra of the action of $p$ is finite projective of rank $p^4$ at all field points. The hypothesis `h0Φ` says that `lieZero` is contained in the kernel of the tangent map of $\varpi$. The hypothesis `hcΦ` says that the $0$- and $1$-graded pieces of the Cartier module of $\Phi$ relative to $\bar\iota$ are complementary additive subgroups, where the $n$-th graded piece consists of those $f$ with $[c]_* f = (\bar\iota([c])^{p^n}) \cdot f$ for all $c \in \mathbb{F}_{p^2}$; this makes the Cartier module of $\Phi$ into graded Cartier module data, whose associated $N$-module is written `NMod`. Finally $r_\Phi \colon (\mathrm{Fin}\,2 \to \mathbb{Z}_p) \to$ `NMod` is an additive map, and `hrΦ` requires that for every canonical $L$-map $L$ on these data, $r_\Phi$ is a bijection of the whole of $(\mathrm{Fin}\,2 \to \mathbb{Z}_p)$ onto the degree-$0$ $\eta$-piece of $L$.
--
--   *The matrix.* $g \in \mathrm{GL}_2(\mathbb{Q}_p)$ has underlying matrix $\mathrm{diag}(p,1)$ (`hg`).
--
--   *Hypotheses on the edge-family module $X$.* $X$ is a formal $O_D$-module over $E$ and $\gamma_0,\gamma_1$ are elements of its Cartier module such that: `hγ` $\gamma$ is a homogeneous $V$-basis for the structure map $E \leftarrow \bar O \leftarrow O$ composed with $\iota$ (each $\gamma_i$ lies in the $i$-th graded piece and the matrix of tangents of the $\gamma_i$ has unit determinant); `hγa` $X$ has structure constants equal to the edge-ring constants built from $\xi$ and $\eta$, i.e. $\varpi_*\gamma_i$ is, to any prescribed $V$-adic order, the corresponding sum $\sum_m V^m([a_{m,i}]\gamma_{\pi(m,i)})$; `hXs` $X$ is special for that structure map; `hX4` $X$ has height $4$.
--
--   *The specialisation $f_0$.* $f_0 \colon E \to \bar O$ is a ring homomorphism splitting the structure map $\bar O \to E$ (`hf₀`) and with $f_0(\xi) = 0$ (`hf₀ξ`) and $f_0(\eta) = 0$ (`hf₀η`).
--
--   *The isogeny from $\Phi$ and its rigidification.* $m$ is a natural number and $\rho_0$ a $2$-tuple of power series over $\bar O$ which is an isogeny $\Phi \to X \otimes_{f_0} \bar O$ of height $4m$ (`hρ₀`). Let $t_0$ denote the rigidified datum with underlying module $X \otimes_{f_0} \bar O$, level $m$ and reduced isogeny $\rho_0 \bmod p$. The hypothesis `hOD₀` says that the reduction of $\rho_0$ is a homomorphism of formal $O_D$-modules from $\bar\Phi$ to $\bar X$ for $t_0$; `hcb` and `hcΦg` say that the $0$- and $1$-graded pieces are complementary for the reduction of $t_0$ along the identity of $\bar O$ and for the corresponding base change of $\Phi$, respectively. Next, $a$ is a natural number and `hN` is the normalisation condition: for each $i \in \{0,1\}$,
--   $$p^{a} \cdot \big(\mathrm{rigidNum}(\iota, h_{c\Phi}, r_\Phi, \dots)\big)(\delta_i) \;=\; p^{a+m} \cdot c_i,$$
--   where $\mathrm{rigidNum}$ is the composite of $r_\Phi$ with the $N$-module maps induced by the base change of $\Phi$ and by the isogeny $\rho_0$, $\delta_i$ is the $i$-th standard vector of $(\mathrm{Fin}\,2 \to \mathbb{Z}_p)$, and $c_0$ is the class `nMk` of $(\gamma_0, 0)$ and $c_1$ is `nVarpi` applied to the class `nMk` of $(\gamma_1, 0)$, the $\gamma_i$ being first transported along $f_0$ and the relevant reductions modulo $p$.
--
--   *The edge isogeny $\rho_1$.* $\rho_1$ is a homomorphism of formal $O_D$-modules from $(X \otimes_{f_0} \bar O) \otimes_{\bar O} E$ to $X$ such that, on Cartier modules, the images of the base changes of $\gamma_0$ and $\gamma_1$ are
--   $$p\,\gamma_0 - V\big([\eta^{p^2}]\,\gamma_1\big), \qquad p\,\gamma_1 - V\big([\xi^{p^2}]\,\gamma_0\big)$$
--   respectively (`hρ₁0`, `hρ₁1`, with $[\cdot]$ the Teichmüller lift and $V$ the integral Verschiebung), and such that $\rho_1$ is an isogeny of height $4$ (`hρ₁h`).
--
--   *The geometric point.* $\Omega$ is an algebraically closed field which is a $\mathbb{Z}_p$-algebra, and $y \colon E \to \Omega$ is a ring homomorphism with $y(\xi) = 0$ (`hyξ`) and $y(\eta) \neq 0$ (`hyη`): the point lies on the $\eta$-branch of the edge family. $Q$ is a Drinfeld datum over $\Omega$ for $K = \mathbb{Q}_p$, $\mathcal{O} = \mathbb{Z}_p$ and uniformiser $p$, consisting of two families of full $\mathbb{Z}_p$-lattices $N_0(x) \le N_1(x)$ in $\mathbb{Q}_p^2$ indexed by $x \in \mathrm{Spec}\,\Omega$, two invertible $\Omega$-modules $T_0, T_1$ with maps $\Pi_0, \Pi_1$ composing to $p$, and stalkwise maps $u_0(x), u_1(x)$ from the base changes of the lattices to the stalks of $T_0, T_1$, subject to the compatibilities recorded in the structure. The hypothesis `hQ` says that the rigidified datum with underlying module $X$, level $m+1$ and isogeny the composite of the reductions of $\rho_0$ and $\rho_1$, pushed forward along $y$, is a Cartier quadruple for $Q$ relative to $\iota$, `hcΦ`, $r_\Phi$ and the structure map $y \circ (\bar O \to E) \circ (O \to \bar O)$: that is, the isogeny is a homomorphism of formal $O_D$-modules, $Q.T_0$ and $Q.T_1$ are identified with the two tangent pieces of the module compatibly with $\Pi_0$, $\Pi_1$ and the tangent action of $\varpi$, and at every prime the lattices $N_0$, $N_1$ consist exactly of those vectors admitting $\eta$-sections of the relevant degree, the maps $u_0$, $u_1$ being computed from the corresponding classes in the graded Cartier module data.
--
--   *The vertex.* $x$ is a point of $\mathrm{Spec}\,\Omega$, and the hypotheses `h₀` and `h₁` say that both $N_0(x)$ and $N_1(x)$ equal the underlying submodule of $p^{-1}\,g\,\mathbb{Z}_p^2$, namely the image of the standard full lattice under $g$ scaled by the inverse of the unit of $\mathbb{Q}_p$ attached to $p$.
--
--   *Conclusion.* Write $\Omega_x =$ `locRing Ω x` for the local ring of $\Omega$ at $x$, and $e_0, e_1$ for the standard basis vectors of the standard full lattice. Let $w$ denote the element of $\Omega_x \otimes_{\mathbb{Z}_p} p^{-1} g\,\mathbb{Z}_p^2$ obtained from
--   $$1 \otimes e_0 + y(\eta) \otimes e_1$$
--   by applying in turn the base-change isomorphism along $g$ and the base-change isomorphism along the scalar matrix $p^{-1}$. Then two assertions hold simultaneously: the kernel of $u_0(x)$ is the $\Omega_x$-span of the single element obtained from $w$ by transport along `h₀.symm` into the base change of the full lattice $Q.L_0\,x$ (whose underlying module is $N_0(x)$); and the kernel of $u_1(x)$ is the $\Omega_x$-span of the single element obtained from the same $w$ by transport along `h₁.symm` into the base change of $Q.L_1\,x$.
--
--   This is the $\eta$-branch half of the local computation of the Drinfeld line in the Čerednik–Drinfeld uniformisation: at a point of the edge chart where $\xi$ vanishes and $\eta$ does not, and where both lattices of the quadruple are the odd vertex $p^{-1}g\mathbb{Z}_p^2$, the kernels of the two stalk maps are the explicit line generated by $e_0 + y(\eta)e_1$. It combines the generic kernel-at-a-point lemmas for Cartier quadruples with the existence of $\eta$-sections in degrees $0$ and $1$ for the edge isogeny, and feeds the assembly [`CerednikDrinfeld.FormalODModule.exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_ne_zero`](thm.html#CerednikDrinfeld.FormalODModule.exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_eq_zero_of_apply_eta_ne_zero.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_eq_zero_of_apply_eta_ne_zero
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
    (hyξ : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hyη : y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ≠ 0)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω)
    (hQ : ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsCartierQuadruple ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) Q)
    (x : PrimeSpectrum Ω)
    (h₀ : Q.N₀ x = (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]))).1)
    (h₁ : Q.N₁ x = (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]))).1) :
        LinearMap.ker (Q.u₀ x) = Submodule.span (locRing Ω x)
          {transportEquiv (locRing Ω x)
              (M₁ := (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p])))) (M₂ := Q.L₀ x) h₀.symm
            (actBaseChange (locRing Ω x) (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
              (FullLattice.act g (stdFullLattice ℚ_[p]))
              (actBaseChange (locRing Ω x) g (stdFullLattice ℚ_[p])
                ((1 : locRing Ω x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + algebraMap Ω (locRing Ω x) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)))} ∧
        LinearMap.ker (Q.u₁ x) = Submodule.span (locRing Ω x)
          {transportEquiv (locRing Ω x)
              (M₁ := (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p])))) (M₂ := Q.L₁ x) h₁.symm
            (actBaseChange (locRing Ω x) (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
              (FullLattice.act g (stdFullLattice ℚ_[p]))
              (actBaseChange (locRing Ω x) g (stdFullLattice ℚ_[p])
                ((1 : locRing Ω x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + algebraMap Ω (locRing Ω x) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)))} := by sorry
