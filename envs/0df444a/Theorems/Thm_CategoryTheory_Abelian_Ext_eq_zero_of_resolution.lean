-- Prove2me | Theorems.Thm_CategoryTheory_Abelian_Ext_eq_zero_of_resolution
-- name    : CategoryTheory.Abelian.Ext.eq_zero_of_resolution
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:15:23.958976+00:00
-- url     : https://prove2.me/theorems/7adb0f4c-bccb-42e3-9fbc-4a9a6290f410
-- title:
--   Vanishing of an Ext class via a resolution: low-degree acyclicity of the terms plus a cocycle-is-coboundary condition
-- statement:
--   Let $\mathcal{C}$ be an abelian category with Ext groups, let $Z, G$ be objects of $\mathcal{C}$ and $m \ge 0$. Let
--   $$\cdots \xrightarrow{d_1} T_1 \xrightarrow{d_0} T_0 \xrightarrow{\varepsilon} Z \to 0$$
--   be a resolution of $Z$: morphisms $d_n : T_{n+1} \to T_n$ and $\varepsilon : T_0 \to Z$ with $d_n \circ d_{n+1} = 0$ and $\varepsilon \circ d_0 = 0$, such that $\varepsilon$ is an epimorphism, the sequence $T_1 \to T_0 \to Z$ is exact, and each sequence $T_{n+2} \to T_{n+1} \to T_n$ is exact. Assume that
--   1. $\operatorname{Ext}^q(T_n, G) = 0$ for all $n$ and all $q$ with $0 < q < m+1$;
--   2. every cocycle in degree $m+1$ is a coboundary: for every $\varphi : T_{m+1} \to G$ with $\varphi \circ d_{m+1} = 0$ there is $\psi : T_m \to G$ with $\varphi = \psi \circ d_m$.
--
--   Then every class $\xi \in \operatorname{Ext}^{m+1}(Z, G)$ whose pullback along $\varepsilon$ vanishes is itself zero:
--   $$\varepsilon^* \xi = 0 \in \operatorname{Ext}^{m+1}(T_0, G) \implies \xi = 0.$$
--
--   This is the low-degree part of the standard computation of Ext through a resolution by objects that are acyclic up to degree $m$; in the project it replaces a Čech-to-derived-functor spectral sequence argument in degrees $\le m+1$.
--
--   **Formalization Note** The category has `[HasExt.{w} C]`, with Ext groups in universe `w`. The pullback $\varepsilon^*\xi$ is written `(mk₀ ε).comp ξ (zero_add (m + 1))`. Vanishing of Ext groups is phrased as `Subsingleton`. Exactness is stated through `ShortComplex.Exact` of the short complexes `T 1 ⟶ T 0 ⟶ Z` and `T (n + 2) ⟶ T (n + 1) ⟶ T n`; Lean composition `d (m + 1) ≫ φ` means $\varphi \circ d_{m+1}$. The Lean name is `CategoryTheory.Abelian.Ext.eq_zero_of_resolution`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/Resolution.lean, lines 35-99 (`CategoryTheory.Abelian.Ext.eq_zero_of_resolution`).

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory
namespace Abelian
namespace Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem eq_zero_of_resolution {Z G : C} (m : ℕ)
    (T : ℕ → C) (d : ∀ n, T (n + 1) ⟶ T n) (ε : T 0 ⟶ Z)
    (hdd : ∀ n, d (n + 1) ≫ d n = 0) (hdε : d 0 ≫ ε = 0) (hε : Epi ε)
    (hex0 : (ShortComplex.mk (d 0) ε hdε).Exact)
    (hexs : ∀ n, (ShortComplex.mk (d (n + 1)) (d n) (hdd n)).Exact)
    (hT : ∀ (n q : ℕ), 0 < q → q < m + 1 → Subsingleton (Ext (T n) G q))
    (hcoc : ∀ (φ : T (m + 1) ⟶ G), d (m + 1) ≫ φ = 0 → ∃ ψ : T m ⟶ G, φ = d m ≫ ψ)
    (ξ : Ext Z G (m + 1))
    (hξ : (mk₀ ε).comp ξ (zero_add (m + 1)) = 0) :
    ξ = 0 := by sorry

end Ext
end Abelian
end CategoryTheory
