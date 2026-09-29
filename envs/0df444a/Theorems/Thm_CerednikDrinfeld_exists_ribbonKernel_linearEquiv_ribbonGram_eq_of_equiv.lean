-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv
-- name    : CerednikDrinfeld.exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/b8a7aeaf-bb89-5f5c-8420-b09701eab46d
-- title:
--   Isomorphic degeneracy data have isometric ribbon kernels
-- statement:
--   Let $E_1,V_1,E_2,V_2$ be types with $E_1,E_2$ finite and equality decidable on $V_1,V_2$, and let $D_1$ be a `DegeneracyData` on $(E_1,V_1)$ and $D_2$ one on $(E_2,V_2)$; thus $D_i$ consists of two maps $a_i,b_i : E_i \to V_i$ and a width function $w_i : E_i \to \mathbb{Z}_{>0}$. For such data, `ribbonKernel` $D_i$ is the submodule of $\mathbb{Z}^{E_i}$ cut out as the intersection of the kernels of the two pushforward maps $\mathbb{Z}^{E_i} \to \mathbb{Z}^{V_i}$ attached to $a_i$ and $b_i$ (each sending $x$ to the function $v \mapsto \sum_{e} [f(e)=v]\,x(e)$), and `ribbonGram` $D_i$ is the restriction to this submodule of the width pairing $\langle x,y\rangle_{D_i} = \sum_{e \in E_i} w_i(e)\,x(e)\,y(e)$, viewed as a map into the $\mathbb{Z}$-dual. Assume given bijections $e_E : E_1 \simeq E_2$ and $e_V : V_1 \simeq V_2$ with $a_2(e_E e) = e_V(a_1 e)$, $b_2(e_E e) = e_V(b_1 e)$ and $w_2(e_E e) = w_1(e)$ for every $e \in E_1$. Then there exists a $\mathbb{Z}$-linear equivalence $\varphi$ from `ribbonKernel` $D_1$ onto `ribbonKernel` $D_2$ such that $(\varphi x)(e_E e) = x(e)$ for all $x$ in the first kernel and all $e \in E_1$, and such that $\langle \varphi x, \varphi y\rangle_{D_2} = \langle x,y\rangle_{D_1}$ for all $x,y$ in the first kernel.
--
--   The statement records that the ribbon kernel of a pair of degeneracy maps with widths, together with its width (monodromy/Gram) pairing, depends on the data only up to isomorphism of the underlying weighted bipartite combinatorial datum. It is used to transport a ribbon kernel presented on one pair of index types to another presentation, in the lemmas on realisations and quotient presentations of the class set with Hecke action in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv.lean

import Definitions.Def_CerednikDrinfeld_Ribbon

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [DecidableEq V₁] [Fintype E₂] [DecidableEq V₂]
    (D₁ : DegeneracyData E₁ V₁) (D₂ : DegeneracyData E₂ V₂)
    (eE : E₁ ≃ E₂) (eV : V₁ ≃ V₂)
    (ha : ∀ e, D₂.a (eE e) = eV (D₁.a e)) (hb : ∀ e, D₂.b (eE e) = eV (D₁.b e)) (hw : ∀ e, D₂.w (eE e) = D₁.w e) :
    ∃ φ : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₂),
      (∀ (x : ↥(ribbonKernel D₁)) (e : E₁), (φ x : E₂ → ℤ) (eE e) = (x : E₁ → ℤ) e) ∧
      (∀ x y : ↥(ribbonKernel D₁), ribbonGram D₂ (φ x) (φ y) = ribbonGram D₁ x y) := by sorry
