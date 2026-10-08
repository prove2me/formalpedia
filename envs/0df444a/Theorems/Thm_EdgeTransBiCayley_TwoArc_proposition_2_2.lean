-- Prove2me | Theorems.Thm_EdgeTransBiCayley_TwoArc_proposition_2_2
-- name    : EdgeTransBiCayley.TwoArc.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:24.118462+00:00
-- url     : https://prove2.me/theorems/1d0dd9b8-c157-4a01-bb87-2218ca8a5733
-- title:
--   Proposition 2.2 — N_Aut(Γ)(R(H)) = R(H)·(F ∪ I) for connected BiCay(H, R, L, S)
-- statement:
--   Let $H$ be a finite group and $\Gamma = \mathrm{BiCay}(H,R,L,S)$ a connected bi-Cayley graph, and write $X = N_{\mathrm{Aut}(\Gamma)}(R(H))$. Let $\mathrm{F}$ be the set of permutations $\sigma_{\alpha,g}$ with $R^\alpha = R$, $L^\alpha = g^{-1}Lg$, $S^\alpha = g^{-1}S$, and $\mathrm{I}$ the set of permutations $\delta_{\alpha,x,y}$ with $R^\alpha = x^{-1}Lx$, $L^\alpha = y^{-1}Ry$, $S^\alpha = y^{-1}S^{-1}x$. Then:
--
--   1. every $\sigma_{\alpha,g} \in \mathrm{F}$ is an automorphism of $\Gamma$ lying in $X$;
--   2. every $\delta_{\alpha,x,y} \in \mathrm{I}$ is an automorphism of $\Gamma$ lying in $X$;
--   3. every element of $X$ is a product $R(h)\,\sigma_{\alpha,g}$ with $\sigma_{\alpha,g}\in\mathrm{F}$ or $R(h)\,\delta_{\alpha,x,y}$ with $\delta_{\alpha,x,y}\in\mathrm{I}$ (first $R(h)$, then the second factor), for some $h \in H$.
--
--   Together:
--   $$N_{\mathrm{Aut}(\Gamma)}(R(H)) = R(H)\,(\mathrm{F} \cup \mathrm{I}).$$
--   This is the first sentence of the proposition: it says $X = R(H) \rtimes \mathrm{F}$ when $\mathrm{I} = \emptyset$ and $X = R(H)\langle \mathrm{F}, \delta_{\alpha,x,y}\rangle$ for any $\delta_{\alpha,x,y} \in \mathrm{I}$ otherwise.
--
--   The paper cites this description of the normaliser from Zhou and Feng; every later statement of the mission about $X$ rests on it.
--
--   **Formalization Note** "$\sigma_{\alpha,g}$ is an element of $X$" is stated as: there is a graph automorphism in `normRH D` whose underlying vertex map is $\sigma_{\alpha,g}$. The products are written pointwise, $v \mapsto \sigma_{\alpha,g}(R(h)\,v)$, matching the paper's right-action product $R(h)\sigma_{\alpha,g}$. Part (b) of the printed proposition (a Cayley-graph isomorphism) is not part of this item. Finiteness of $H$ is the paper's standing assumption (§2).
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 5, Proposition 2.2 (first sentence; cited there from [55, Theorem 1.1])

import Mathlib
import Definitions.Def_EdgeTransBiCayley_TwoArc_Setting
open Pointwise

namespace EdgeTransBiCayley.TwoArc

theorem proposition_2_2 {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (D : BiCayData H) (hconn : D.graph.Connected) :
    (∀ (α : MulAut H) (g : H), IsF D α g →
      ∃ φ ∈ normRH D, ∀ v, φ v = sigmaPerm α g v) ∧
    (∀ (α : MulAut H) (x y : H), IsI D α x y →
      ∃ φ ∈ normRH D, ∀ v, φ v = deltaPerm α x y v) ∧
    (∀ φ ∈ normRH D,
      (∃ (α : MulAut H) (g h : H), IsF D α g ∧
          ∀ v, φ v = sigmaPerm α g (rightMul D h v)) ∨
      (∃ (α : MulAut H) (x y h : H), IsI D α x y ∧
          ∀ v, φ v = deltaPerm α x y (rightMul D h v))) := by sorry

end EdgeTransBiCayley.TwoArc
