-- Prove2me | Theorems.Thm_BoundedDegreeST_PlusOne_claim_4_5
-- name    : BoundedDegreeST.PlusOne.claim_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:50.684991+00:00
-- url     : https://prove2.me/theorems/7daae5cb-59b3-4166-b120-b7169b740b15
-- title:
--   Claim 4.5 — vertices with one excess token
-- statement:
--   In the contradiction setting of Lemma 4.1, let $x^*$ be a basic feasible LP solution and let $(\mathcal L,T)$ be its laminar basis. Suppose no supported edge has value $1$ and every $w\in W$ has $\deg_{E^*}(w)>B_w+1$. For an active vertex $v$, define its excess tokens as $\deg_{E^*}(v)-2$ when $v\in T$, and as $\deg_{E^*}(v)$ otherwise. If it has exactly one excess token, then
--
--   $$
--   (v\notin T\ 	ext{and}\ \deg_{E^*}(v)=1)\quad\text{or}\quad(v\in T,\ \deg_{E^*}(v)=3,\ B_v=1).
--   $$
--
--   This restricts the low-token cases in the counting lemma.
--
--   **Formalization Note** The preterminal and contradiction assumptions from the surrounding proof are explicit hypotheses.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 667, Claim 4.5

import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Claim 4.5, p. 667. -/
theorem claim_4_5 {V : Type*} [Fintype V] [DecidableEq V]
    (I : Instance V) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) (v : V)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F)
    (hbasis : DefinesBasis I.E I.B I.W I.F x L T)
    (hnoone : ∀ e ∈ support I.E x, x e ≠ 1)
    (hnosmall : ∀ w ∈ I.W, (degree (support I.E x) w : ℤ) > I.B w + 1)
    (hactive : 0 < degree (support I.E x) v)
    (hone : excessTokens (support I.E x) T v = 1) :
    (v ∉ T ∧ degree (support I.E x) v = 1) ∨
    (v ∈ T ∧ degree (support I.E x) v = 3 ∧ I.B v = 1) := by sorry
end BoundedDegreeST.PlusOne
