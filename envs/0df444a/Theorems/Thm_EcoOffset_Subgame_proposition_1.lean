-- Prove2me | Theorems.Thm_EcoOffset_Subgame_proposition_1
-- name    : EcoOffset.Subgame.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:05.375936+00:00
-- url     : https://prove2.me/theorems/bf7967c6-445a-4a6b-ae22-d9f77ceb2a43
-- title:
--   Proposition 1, pp. 13–14 (PDF 14–15) — in Cases N and P a lower offset price can raise abatement (e∗(g1) ≤ e∗(g2), g1 < g2) by expanding coverage
-- statement:
--   Assume the standing assumptions of the model, and let $\pi(p,e,t\mid g)$ be the firm's profit at the offset price $g$, $e_{x,a}$ the segment-optimal emission, and $h$ the function of the relevant case.
--
--   **(i) Case N** ($\beta_u=1$). Suppose $\alpha>0$ and $\beta_c<B_2$. Let $X>0$ be the least zero of
--   $$h(g)=\pi(v_l,e_{g,1},e_{g,1}+e_o\mid g)-\pi(v_h,e_{g,a_N},e_{g,a_N}+e_o\mid g),\qquad a_N=1-\alpha+\alpha\beta_c,$$
--   suppose $h$ changes sign at $X$ (every right neighbourhood of $X$ contains a $g$ with $h(g)<0$), $X<\xi$, and condition (1), i.e. $\pi(v_l,e_{X,1},e_{X,1}+e_o\mid X)>(v_h-c(\bar e))(1-\alpha)m$ (the proof's "$\beta_c>B_1$"). Then there are offset prices $0<g_1<g_2$ at which best responses exist, and for every best response $(p_1,e_1,t_1)$ to $g_1$ and every best response $(p_2,e_2,t_2)$ to $g_2$:
--   1. the firm buys offsets at both prices: $t_1>0$, $t_2>0$;
--   2. controllable emissions are lower at the lower offset price: $e_1\le e_2$, and $e_1<e_2$ if $e_{X,1}<\bar e$ and $e_{X,a_N}>0$;
--   3. $d_u^*(g_1)=d_u^*(g_2)$ and $d_c^*(g_1)>d_c^*(g_2)$.
--
--   **(ii) Case P** ($\beta_c=1$). Suppose $\alpha<1$, $v_h-v_l<\xi e_o$ and $\beta_u<\tilde B_2$. Let $X>0$ be the least zero of
--   $$h(g)=\pi\big(v_l,e_{g,1},e_{g,1}+e_o-\tfrac{v_h-v_l}{\xi}\;\big|\;g\big)-\pi(v_h,e_{g,a_P},e_{g,a_P}+e_o\mid g),\qquad a_P=\alpha+(1-\alpha)\beta_u,$$
--   suppose $h$ changes sign at $X$, $X<\xi$, and condition (1), i.e. $\pi(v_h,e_{X,a_P},e_{X,a_P}+e_o\mid X)>\max\big((v_h-c(\bar e))(1-\alpha)\beta_u m,(v_l-c(\bar e))(1-\alpha)m\big)$ (the proof's "$\beta_u>\tilde B_1$"). Then there are $0<g_1<g_2$ with best responses at both, and every pair of best responses satisfies $t_1,t_2>0$, $e_1\le e_2$ (strict if $e_{X,1}<\bar e$ and $e_{X,a_P}>0$), $d_c^*(g_1)=d_c^*(g_2)$ and $d_u^*(g_1)>d_u^*(g_2)$.
--
--   In words: in both the negatively and the positively correlated case, a cheaper offset can lead the firm to cut its controllable emissions, because the cheaper offset lets it lower its footprint enough to serve an additional segment, and the larger volume makes abatement (a fixed cost) more worthwhile.
--
--   **Formalization Note**
--   1. The paper's "$\beta_c\in(B_1,B_2)$ for some $B_1,B_2\ge0$" would be satisfied vacuously by $B_1=B_2$; it is stated with the proof's explicit $B_2$ and with condition (1), which the proof identifies with $\beta_c>B_1$ (and analogously in Case P).
--   2. The paper writes the best responses $p^*(g),e^*(g),t^*(g)$ as functions; the statement asserts existence and quantifies over every best response, which includes uniqueness at $g_1,g_2$.
--   3. "Suppose the firm chooses to purchase offsets" becomes the conclusion $t_1,t_2>0$.
--   4. Added hypotheses, all disclosed: $X<\xi$ (the proof's "then we must have $X<G$" is not proved, and numerical instances of Case N violate it); the sign change of $h$ at $X$ (the proof asserts $\partial h/\partial g|_{g=X}<0$ without proof); $\alpha>0$ in (i) and $\alpha<1$ in (ii), because $B_2$ and $\tilde B_2$ divide by them.
--   5. "Strict if $\bar e$ is large enough" is made precise as $e_{X,1}<\bar e$ and $0<e_{X,a}$.
--   6. $\beta_c<B_2$ is implied by the hypotheses on $X$ but is kept because it is the paper's hypothesis.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), pp. 13–14 (PDF 14–15), Proposition 1; proof on Online Supplement pp. 24–26 (PDF 57–59)

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Proposition 1 (Gao & Souza, pp. 13–14). (i) Case N (`βu = 1`): if `βc < B2`, the least zero
`X` of `h` is a sign change, `X < ξ`, and condition (1) holds at `X` (the proof's "βc > B1"),
then there are offset prices `0 < g1 < g2` at which best responses exist, and every pair of best
responses buys offsets, has `e*(g1) ≤ e*(g2)` (strict when `e_{X,1} < ¯e` and `0 < e_{X,aN}`),
`d_u*(g1) = d_u*(g2)` and `d_c*(g1) > d_c*(g2)`. (ii) Case P (`βc = 1`): the analogue with
`vh − vl < ξ eo`, `βu < ˜B2`, and `d_c*(g1) = d_c*(g2)`, `d_u*(g1) > d_u*(g2)`. -/
theorem proposition_1 (P : Params) (hS : P.Standing) :
    -- (i) Case N
    (P.βu = 1 → 0 < P.α → P.βc < B2 P →
      ∀ X : ℝ, 0 < X → hN P X = 0 → (∀ g ∈ Set.Ico 0 X, 0 < hN P g) →
      (∀ ε > 0, ∃ g ∈ Set.Ioo X (X + ε), hN P g < 0) →
      X < P.ξ →
      valOne P < valAll P X →
      ∃ g1 g2 : ℝ, 0 < g1 ∧ g1 < g2 ∧
        (∃ p e t, IsBestResponse P g1 p e t) ∧ (∃ p e t, IsBestResponse P g2 p e t) ∧
        ∀ p1 e1 t1 p2 e2 t2, IsBestResponse P g1 p1 e1 t1 → IsBestResponse P g2 p2 e2 t2 →
          0 < t1 ∧ 0 < t2 ∧ e1 ≤ e2 ∧
          demandU P p1 e1 t1 = demandU P p2 e2 t2 ∧
          demandC P p2 e2 t2 < demandC P p1 e1 t1 ∧
          (segOpt P X 1 < P.ebar → 0 < segOpt P X (aN P) → e1 < e2)) ∧
    -- (ii) Case P
    (P.βc = 1 → P.α < 1 → P.vh - P.vl < P.ξ * P.eo → P.βu < B2P P →
      ∀ X : ℝ, 0 < X → hP P X = 0 → (∀ g ∈ Set.Ico 0 X, 0 < hP P g) →
      (∀ ε > 0, ∃ g ∈ Set.Ioo X (X + ε), hP P g < 0) →
      X < P.ξ →
      max (valOne P) (valThree P) < valTwoP P X →
      ∃ g1 g2 : ℝ, 0 < g1 ∧ g1 < g2 ∧
        (∃ p e t, IsBestResponse P g1 p e t) ∧ (∃ p e t, IsBestResponse P g2 p e t) ∧
        ∀ p1 e1 t1 p2 e2 t2, IsBestResponse P g1 p1 e1 t1 → IsBestResponse P g2 p2 e2 t2 →
          0 < t1 ∧ 0 < t2 ∧ e1 ≤ e2 ∧
          demandC P p1 e1 t1 = demandC P p2 e2 t2 ∧
          demandU P p2 e2 t2 < demandU P p1 e1 t1 ∧
          (segOpt P X 1 < P.ebar → 0 < segOpt P X (aP P) → e1 < e2)) := by sorry

end EcoOffset.Subgame
