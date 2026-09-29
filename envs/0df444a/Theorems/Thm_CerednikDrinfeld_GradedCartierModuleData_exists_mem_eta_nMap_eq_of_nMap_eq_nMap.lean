-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_mem_eta_nMap_eq_of_nMap_eq_nMap
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_mem_eta_nMap_eq_of_nMap_eq_nMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/c859312e-fa3f-5588-939c-75a414387f72
-- title:
--   Gluing η(L) along a Milnor square of Cartier data
-- statement:
--   Fix a prime $p$ and write $\mathbb{Z}_{p^2}$ for $W(\mathbb{F}_{p^2})$. Let $B,B_0,B_1,B_{01}$ be commutative rings, each equipped with a ring map from $\mathbb{Z}_{p^2}$, and let $D,D_0,D_1,D_{01}$ be graded Cartier module data over them: modules $M$ over $W(p,B)$ carrying additive $F$, $V$, a $W$-linear $\varpi$ with the usual Cartier relations and a decomposition into two complementary pieces permuted by $F,V,\varpi$. Let $f_0\colon M\to M_0$, $f_1\colon M\to M_1$, $g_0\colon M_0\to M_{01}$, $g_1\colon M_1\to M_{01}$ be additive maps, each commuting with $V$ and with $\varpi$, such that $g_0f_0=g_1f_1$, that $f_0m=f_1m=0$ forces $m=0$, that every pair $(m_0,m_1)$ with $g_0m_0=g_1m_1$ is of the form $(f_0m,f_1m)$, that $g_0$ is surjective, and that $V$ is injective on $M_{01}$. Let $L,L_0,L_1$ satisfy `IsCartierLMap` for $D,D_0,D_1$ (Frobenius-semilinearity, $L(Vx)=\mathrm{nMk}(\varpi x,0)$, $\lambda\circ L=F$), with $L_0\circ f_0=N(f_0)\circ L$ and $L_1\circ f_1=N(f_1)\circ L$, where $N(M)=(M\oplus M^{\sigma})/\{(Vm,-\varpi m)\}$ and $N(f)$ is the induced map. If $z_0\in N(M_0)$ and $z_1\in N(M_1)$ are fixed by the respective endomorphisms `phi` attached to $L_0,L_1$ (that is, lie in `eta`) and satisfy $N(g_0)z_0=N(g_1)z_1$, then some $z\in N(M)$ fixed by `phi` attached to $L$ satisfies $N(f_0)z=z_0$ and $N(f_1)z=z_1$.
--
--   This is the gluing statement for the $\varphi_L$-invariant subgroups $\eta(L)\subseteq N(M)$ of graded Cartier module data along a Milnor (fibre-product) square of base rings, as used in the Čerednik–Drinfeld uniformisation in the form given by Boutot and Carayol. It is invoked by [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_mem_etaPiece_smul_eq_of_smul_eq_nMap_quotient_of_inf_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_mem_eta_nMap_eq_of_nMap_eq_nMap.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.exists_mem_eta_nMap_eq_of_nMap_eq_nMap
    (p : ℕ) [Fact p.Prime]
    {B B₀ B₁ B₀₁ : Type} [CommRing B] [CommRing B₀] [CommRing B₁] [CommRing B₀₁]
    {j : Zp2 p →+* B} {j₀ : Zp2 p →+* B₀} {j₁ : Zp2 p →+* B₁} {j₀₁ : Zp2 p →+* B₀₁}
    (D : GradedCartierModuleData p B j) (D₀ : GradedCartierModuleData p B₀ j₀)
    (D₁ : GradedCartierModuleData p B₁ j₁) (D₀₁ : GradedCartierModuleData p B₀₁ j₀₁)
    (f₀ : D.M →+ D₀.M) (f₁ : D.M →+ D₁.M) (g₀ : D₀.M →+ D₀₁.M) (g₁ : D₁.M →+ D₀₁.M)
    (hf₀V : ∀ m, f₀ (D.verschiebung m) = D₀.verschiebung (f₀ m)) (hf₀P : ∀ m, f₀ (D.varpi m) = D₀.varpi (f₀ m))
    (hf₁V : ∀ m, f₁ (D.verschiebung m) = D₁.verschiebung (f₁ m)) (hf₁P : ∀ m, f₁ (D.varpi m) = D₁.varpi (f₁ m))
    (hg₀V : ∀ m, g₀ (D₀.verschiebung m) = D₀₁.verschiebung (g₀ m)) (hg₀P : ∀ m, g₀ (D₀.varpi m) = D₀₁.varpi (g₀ m))
    (hg₁V : ∀ m, g₁ (D₁.verschiebung m) = D₀₁.verschiebung (g₁ m)) (hg₁P : ∀ m, g₁ (D₁.varpi m) = D₀₁.varpi (g₁ m))
    (hsq : ∀ m, g₀ (f₀ m) = g₁ (f₁ m))
    (hinj : ∀ m : D.M, f₀ m = 0 → f₁ m = 0 → m = 0)
    (hglue : ∀ (m₀ : D₀.M) (m₁ : D₁.M), g₀ m₀ = g₁ m₁ → ∃ m : D.M, f₀ m = m₀ ∧ f₁ m = m₁)
    (hg₀s : Function.Surjective g₀)
    (hV₀₁ : Function.Injective D₀₁.verschiebung)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L)
    (L₀ : D₀.M →+ D₀.NMod) (hL₀ : D₀.IsCartierLMap L₀)
    (L₁ : D₁.M →+ D₁.NMod) (hL₁ : D₁.IsCartierLMap L₁)
    (hLL₀ : ∀ m, L₀ (f₀ m) = D.nMap D₀ f₀ hf₀V hf₀P (L m))
    (hLL₁ : ∀ m, L₁ (f₁ m) = D.nMap D₁ f₁ hf₁V hf₁P (L m))
    (z₀ : D₀.NMod) (hz₀ : z₀ ∈ D₀.eta L₀ hL₀.map_verschiebung)
    (z₁ : D₁.NMod) (hz₁ : z₁ ∈ D₁.eta L₁ hL₁.map_verschiebung)
    (hcompat : D₀.nMap D₀₁ g₀ hg₀V hg₀P z₀ = D₁.nMap D₀₁ g₁ hg₁V hg₁P z₁) :
    ∃ z ∈ D.eta L hL.map_verschiebung,
      D.nMap D₀ f₀ hf₀V hf₀P z = z₀ ∧ D.nMap D₁ f₁ hf₁V hf₁P z = z₁ := by sorry
