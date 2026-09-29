-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
-- name    : CerednikDrinfeld.Mumford.exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/3449ebee-98a6-59a6-800a-304f733e08ca
-- title:
--   Transporting a quotient-tree presentation along conjugation by p
-- statement:
--   Let a group $P$ act on a set $W$ carrying a simple graph $\mathcal T$, with every element of $P$ sending adjacent vertices to adjacent vertices, and let $\mathcal T$ be a tree. Let $\tau : W \to \mathbb Z/2$ satisfy $\tau u \neq \tau v$ whenever $u,v$ are adjacent. Let $H \le P$ act on $\mathcal T$ as a graph, with $\tau(h\cdot w) = \tau(w)$ for all $h \in H$, $w \in W$, and let $p \in P$ satisfy $\tau(p\cdot w) = \tau(w)$ for all $w$. Let $G_2 \le P$ act on $\mathcal T$ as a graph with $p^{-1}Hp \subseteq G_2$, and let $\Gamma' \le G_2$ act on $\mathcal T$ as a graph and be characterised by $x \in \Gamma' \iff pxp^{-1} \in H$. Let $E$ be a finite type, $V$ a type with decidable equality, and $D$ a degeneracy datum on $(E,V)$, consisting of maps $a, b : E \to V$ and weights $w : E \to \mathbb Z_{>0}$; write $Z(D) \subseteq (E \to \mathbb Z)$ for the intersection of the kernels of the pushforwards along $a$ and along $b$. Suppose given a bijection $e_E$ of $E$ with those $H$-orbits of darts of $\mathcal T$ whose chosen representative has origin of colour $0$, a bijection $e_V$ of $V$ with the $H$-orbits of $W$, such that for every $e \in E$ the vertex $e_V(a(e))$ is the $H$-orbit of the origin, and $e_V(b(e))$ the $H$-orbit of the terminus, of the chosen representative dart of $e_E(e)$. Suppose further given a base vertex $v_0 \in W$ and a homomorphism $\Phi$ from the additive group underlying $H^{\mathrm{ab}}$ to $Z(D)$ such that, for every $h \in H$, $\Phi$ of the class of $h$ is the function sending $e$ to the sum of the signed multiplicities (via `dartIndex`) of the orbit $e_E(e)$ over the darts of a chosen path from $v_0$ to $h\cdot v_0$, and $0$ if these are not joined by a walk. The conclusion asserts the existence of a bijection $e_E'$ of $E$ with those $\Gamma'$-orbits of darts whose chosen representative has origin of colour $0$, a bijection $e_V'$ of $V$ with the $\Gamma'$-orbits of $W$, and a homomorphism $\Phi'$ from the additive group underlying $\Gamma'^{\mathrm{ab}}$ to $Z(D)$, such that: $e_E'(e)$ is the $\Gamma'$-orbit of $p^{-1}$ applied to the chosen representative dart of $e_E(e)$; whenever $e_V(v)$ is the $H$-orbit of $w$, $e_V'(v)$ is the $\Gamma'$-orbit of $p^{-1}\cdot w$; $e_V'(a(e))$ and $e_V'(b(e))$ are the $\Gamma'$-orbits of the origin and terminus of the chosen representative of $e_E'(e)$; $\Phi'$ of the class of $\gamma$ is the corresponding cycle function computed with the orbits $e_E'$ and the same base vertex $v_0$; and $\Phi'$ of the class of $\gamma$ equals $\Phi$ of the class of $p\gamma p^{-1} \in H$.
--
--   This is the Bass–Serre bookkeeping behind a Hecke correspondence between Mumford quotients: conjugation by a colour-preserving element $p$ identifies the folded quotient graph of $H$ acting on the tree with that of $\Gamma' = p^{-1}Hp$, and transports the cycle map into the ribbon kernel of the degeneracy datum accordingly. It is used in the comparison of period pairings under pullback and pushforward along degeneracy maps of Mumford quotients of Drinfeld's upper half plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle.lean

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Mathlib.GroupTheory.Abelianization.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
    {P : Type} [Group P] {W : Type} [MulAction P W] (𝒯 : SimpleGraph W) [GraphAction P 𝒯] (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    (H : Subgroup P) [GraphAction ↥H 𝒯] (hH : ∀ (h : ↥H) (w : W), τ (h • w) = τ w)
    (p : P) (hp : ∀ w : W, τ (p • w) = τ w)
    (G₂ : Subgroup P) [GraphAction ↥G₂ 𝒯] (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ G₂)
    (Γ' : Subgroup ↥G₂) [GraphAction ↥Γ' 𝒯] (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    [DecidableEq (QuotEdge ↥H 𝒯)] [DecidableEq (QuotEdge ↥Γ' 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge ↥H 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert ↥H W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel ↥H W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel ↥H W) (eE e).1.out.snd)
    (v₀ : W)
    (Φ : Additive (Abelianization ↥H) →+ ↥(ribbonKernel D))
    (hΦ : ∀ h : ↥H, (Φ (Additive.ofMul (Abelianization.of h)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE e).1) v₀ h) :
    ∃ (eE' : E ≃ {e : QuotEdge ↥Γ' 𝒯 // τ e.out.fst = 0}) (eV' : V ≃ QuotVert ↥Γ' W)
      (Φ' : Additive (Abelianization ↥Γ') →+ ↥(ribbonKernel D)),
      (∀ e : E, ((eE' e).1 : QuotEdge ↥Γ' 𝒯) = Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) (p⁻¹ • (eE e).1.out)) ∧
      (∀ v : V, ∀ w : W, eV v = Quotient.mk (orbitRel ↥H W) w → eV' v = Quotient.mk (orbitRel ↥Γ' W) (p⁻¹ • w)) ∧
      (∀ e : E, eV' (D.a e) = Quotient.mk (orbitRel ↥Γ' W) (eE' e).1.out.fst) ∧
      (∀ e : E, eV' (D.b e) = Quotient.mk (orbitRel ↥Γ' W) (eE' e).1.out.snd) ∧
      (∀ γ : ↥Γ', (Φ' (Additive.ofMul (Abelianization.of γ)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE' e).1) v₀ γ) ∧
      (∀ γ : ↥Γ', Φ' (Additive.ofMul (Abelianization.of γ)) =
        Φ (Additive.ofMul (Abelianization.of (⟨p * ((γ : ↥G₂) : P) * p⁻¹, (hΓ' (γ : ↥G₂)).1 γ.2⟩ : ↥H)))) := by sorry
