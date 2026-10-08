-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiDihedrant_proposition_2_2
-- name    : EdgeTransBiCayley.BiDihedrant.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:37.044695+00:00
-- url     : https://prove2.me/theorems/032b0ad8-5bb2-40f3-937d-230aa0759cff
-- title:
--   Proposition 2.2 — N_Aut(Γ)(R(H)) = R(H)·(F ∪ I) for a connected bi-Cayley graph
-- statement:
--   Let $\Gamma = \mathrm{BiCay}(H, R, L, S)$ be a connected bi-Cayley graph over a finite group $H$, and let $X = N_{\mathrm{Aut}(\Gamma)}(R(H))$. With $\mathrm F$ and $\mathrm I$ as in (2.2):
--
--   1. every $\sigma_{\alpha,g} \in \mathrm F$ is an automorphism of $\Gamma$ lying in $X$;
--   2. every $\delta_{\alpha,x,y} \in \mathrm I$ is an automorphism of $\Gamma$ lying in $X$;
--   3. every element of $X$ is of the form $R(h)\,\sigma_{\alpha,g}$ with $\sigma_{\alpha,g} \in \mathrm F$, or $R(h)\,\delta_{\alpha,x,y}$ with $\delta_{\alpha,x,y} \in \mathrm I$, for some $h \in H$ (apply $R(h)$ first).
--
--   Equivalently,
--
--   $$
--   N_{\mathrm{Aut}(\Gamma)}(R(H)) = R(H)\,\mathrm F \ \text{ if } \mathrm I = \emptyset, \qquad N_{\mathrm{Aut}(\Gamma)}(R(H)) = R(H)\langle \mathrm F, \delta_{\alpha,x,y}\rangle \ \text{ if } \delta_{\alpha,x,y} \in \mathrm I.
--   $$
--
--   This description of the normaliser is the tool by which the paper decides when an automorphism of $H$ yields a graph automorphism: in this mission, no automorphism of $H$ may map $S$ to $S^{-1}$ in a semisymmetric graph (Theorem 6.1), and $\sigma_{\alpha,b}$ is an automorphism of $\Gamma(n,\lambda,2k)$ (Example 6.2).
--
--   **Formalization Note** The two printed cases are stated together as $X = R(H)(\mathrm F \cup \mathrm I)$, which says the same: if $\delta \in \mathrm I$ then every $\delta' \in \mathrm I$ lies in $R(H)\langle \mathrm F, \delta\rangle$. Since the paper's maps act on the right, $R(h)\sigma$ means "first $R(h)$, then $\sigma$"; Lean writes `φ v = sigmaPerm α g (rightMul D h v)` pointwise. Parts (a) and (b) of the printed proposition are not used in this mission and are not stated.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 5, Proposition 2.2 (first sentence)

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiDihedrant_Setting
open Pointwise

namespace EdgeTransBiCayley.BiDihedrant

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

end EdgeTransBiCayley.BiDihedrant
