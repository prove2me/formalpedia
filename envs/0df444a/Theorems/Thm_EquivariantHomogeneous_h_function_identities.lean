-- Prove2me | Theorems.Thm_EquivariantHomogeneous_h_function_identities
-- name    : EquivariantHomogeneous.h_function_identities
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:31:54.712196+00:00
-- url     : https://prove2.me/theorems/590c6138-42e3-4c36-b10e-bc2fbfdc5365
-- title:
--   Appendix A, Eqs. (18)-(28): the h-function, its cocycle condition and the decomposition g = s(gH)h(g)
-- statement:
--   Let $G$ be a group, $H\le G$ a subgroup, and $s:G/H\to G$ a section with $s(H)=e$. Let $\mathrm h(x,g)=s(gx)^{-1}g\,s(x)\in H$ and $\mathrm h(g)=\mathrm h(H,g)$. Then for all $x\in G/H$, $g,g_1,g_2\in G$ and $h\in H$:
--
--   1. $g\,s(x)=s(gx)\,\mathrm h(x,g)$ (eq. (18));
--   2. the cocycle condition holds:
--   $$\mathrm h(x,g_1g_2)=\mathrm h(g_2x,g_1)\,\mathrm h(x,g_2)\qquad\text{(eq. (20))};$$
--   3. $\mathrm h(H,h)=h$ (eq. (21)), $\mathrm h(H,s(x))=e$ (eq. (22)) and $\mathrm h(H,s(x)h)=h$ (eq. (23));
--   4. $g=s(gH)\,\mathrm h(g)$ (eq. (26)), and this factorisation is unique: if $g=s(x)k$ with $k\in H$, then $x=gH$ and $k=\mathrm h(g)$;
--   5. $\mathrm h(gh)=\mathrm h(g)\,h$ (eq. (27)) and $\mathrm h(s(x))=e$ (eq. (28)).
--
--   These identities are the calculus used in every later computation with induced representations and kernels.
-- source:
--   Cohen, Geiger and Weiler, A General Theory of Equivariant CNNs on Homogeneous Spaces, arXiv:1811.02017v2 (NeurIPS 2019), Section 2.2, p. 4 (cocycle condition) and Appendix A, Eqs. (18)-(28), pp. 13-14

import Mathlib
import Definitions.Def_EquivariantHomogeneous_Basic

open EquivariantHomogeneous

namespace EquivariantHomogeneous

theorem h_function_identities {G : Type*} [Group G] {H : Subgroup G} (s : CosetSection H) :
    (∀ (x : G ⧸ H) (g : G), g * s.toFun x = s.toFun (g • x) * (hfun s x g : G)) ∧
    (∀ (x : G ⧸ H) (g₁ g₂ : G), hfun s x (g₁ * g₂) = hfun s (g₂ • x) g₁ * hfun s x g₂) ∧
    (∀ h : H, hfun s (QuotientGroup.mk (1 : G)) (h : G) = h) ∧
    (∀ x : G ⧸ H, hfun s (QuotientGroup.mk (1 : G)) (s.toFun x) = 1) ∧
    (∀ (x : G ⧸ H) (h : H), hfun s (QuotientGroup.mk (1 : G)) (s.toFun x * (h : G)) = h) ∧
    (∀ g : G, g = s.toFun (QuotientGroup.mk g) * (hElem s g : G)) ∧
    (∀ (g : G) (x : G ⧸ H) (k : H), g = s.toFun x * (k : G) →
      x = QuotientGroup.mk g ∧ k = hElem s g) ∧
    (∀ (g : G) (h : H), hElem s (g * (h : G)) = hElem s g * h) ∧
    (∀ x : G ⧸ H, hElem s (s.toFun x) = 1) := by sorry

end EquivariantHomogeneous
