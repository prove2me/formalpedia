-- Prove2me | Theorems.Thm_ConstrNestedLogit_Scheme_fractional_utility_le
-- name    : ConstrNestedLogit.Scheme.fractional_utility_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:46.785645+00:00
-- url     : https://prove2.me/theorems/a3df37a6-99be-45f4-8820-1436f3849146
-- title:
--   The fractional product of (17) at J* has utility at most z*(û)/q
-- statement:
--   Fix a nest $i$ with $w_{ij}>0$, a parameter $\hat u\ge0$ and an integer $q\ge1$. Let $S^\ast_i$ be an optimal solution of problem (10) at $\hat u$ with $|S^\ast_i|>q$, write $z^\ast(\hat u)=\sum_{j\in S^\ast_i}v_{ij}(r_{ij}-\hat u)$, and let $J^\ast_i\subseteq S^\ast_i$ consist of $q$ products of $S^\ast_i$ with the largest utilities (every product of $S^\ast_i\setminus J^\ast_i$ has utility at most that of every product of $J^\ast_i$). If $x$ is an optimal solution of problem (17) at $u=\hat u$, $J=J^\ast_i$, and $j'$ is a fractional component, $0<x_{ij'}<1$, then
--
--   $$
--   v_{ij'}(r_{ij'}-\hat u)\le \frac{z^\ast(\hat u)}{q}.
--   $$
--
--   This bounds the utility lost when the fractional product is dropped by rounding down.
--
--   **Formalization Note** $q\ge1$ is added (the paper uses $q=\lceil\alpha/(\alpha-1)\rceil\ge2$; at $q=0$ the division is by zero). $w_{ij}>0$ is added. Ties in "the $q$ largest utilities" may be broken arbitrarily.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, pp. 41–42, Online Supplement C.2, proof of Lemma 8

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Scheme_Model

namespace ConstrNestedLogit.Scheme

/-- Online Supplement C.2, pp. 41–42: let `q ≥ 1`, let `S*` be optimal for problem (10) at `û ≥ 0` with
`|S*| > q`, and let `J*` consist of `q` products of `S*` with the largest utilities. If an
optimal solution of problem (17) at `(û, J*)` has a fractional component `j'`, then
`v_ij' (r_ij' − û) ≤ z*(û)/q`, where `z*(û) = ∑_{j ∈ S*} v_ij (r_ij − û)`. -/
theorem fractional_utility_le {ι : Type*} {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n) (w : ι → Fin n → ℝ) (c : ι → ℝ)
    (hw : ∀ i j, 0 < w i j) (i : ι) (q : ℕ) (hq : 1 ≤ q) (u : ℝ) (hu : 0 ≤ u)
    (Sstar : Finset (Fin n)) (hSfeas : ConstrNestedLogit.Space.spaceFeasible w c i Sstar)
    (hSopt : ∀ S, ConstrNestedLogit.Space.spaceFeasible w c i S → obj10 I i u S ≤ obj10 I i u Sstar)
    (hcard : q < Sstar.card)
    (Jstar : Finset (Fin n)) (hJsub : Jstar ⊆ Sstar) (hJcard : Jstar.card = q)
    (hJtop : ∀ j ∈ Jstar, ∀ k ∈ Sstar \ Jstar, ConstrNestedLogit.Space.utility I i u k ≤ ConstrNestedLogit.Space.utility I i u j)
    (x : Fin n → ℝ) (hx : optimal17 I w c i u Jstar x)
    (j' : Fin n) (hj'0 : 0 < x j') (hj'1 : x j' < 1) :
    ConstrNestedLogit.Space.utility I i u j' ≤ obj10 I i u Sstar / q := by sorry

end ConstrNestedLogit.Scheme
