-- Prove2me | Theorems.Thm_FlowAllocationGames_UnitRanking_proposition_5_circulation
-- name    : FlowAllocationGames.UnitRanking.proposition_5_circulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:34:22.510627+00:00
-- url     : https://prove2.me/theorems/752f1a5f-a291-4ac6-899a-3e4f9d4831fa
-- title:
--   Proposition 5 — feasible flows are circulations in $G'$
-- statement:
--   Let $a$ be a strategy profile of a flow allocation game, with real strategies $a_e : \mathbb R_{\ge 0} \to \mathbb R_{\ge 0}$ that satisfy the capacity constraint $a_e(y) \le c_e$ and the no-fraud constraint $\sum_{e\in E^+(v)} a_e(y) = \min\{c^+_v, y\}$, and let $f \ge 0$ be a feasible flow of $a$: $f_e = a_e(f_v)$ for every edge $e$ with tail $v$, where $f_v = b_v + \sum_{e\in E^-(v)} f_e$. In the network $G'$, put $f$ on the edges of $G$, the non-forwarded flow $f_v - \sum_{e\in E^+(v)} f_e$ on the auxiliary edge $(v, s)$ and the supply $b_v$ on $(s, v)$ (so every $(s,v)$ is saturated). Then
--
--   1. every node forwards at most its total supply, $\sum_{e\in E^+(v)} f_e \le f_v$, so the flow on $(v, s)$ is nonnegative and flow is conserved at $v$;
--   2. every edge of $G$ carries at most its capacity, $f_e \le c_e$;
--   3. the incoming flow of $s$ is
--   $$
--   \sum_{v\in V}\Bigl(f_v - \sum_{e\in E^+(v)} f_e\Bigr) = \sum_{v \in V} b_v ,
--   $$
--   equal to its outgoing flow, so flow is conserved at $s$.
--
--   Hence the flow on $G'$ is a circulation with all auxiliary edges $(s, v)$ saturated.
--
--   Differences from the source:
--   - reading: the corresponding flow in G′ can be decomposed and represented as a circulation; s has incoming flow Σ bv; all (s, v) saturated → with f on E, fv − Σ_{E⁺(v)} f on (v, s) and bv on (s, v): Σ_{E⁺(v)} f ≤ fv for every v, f ≤ c on E, and Σ_v (fv − Σ_{E⁺(v)} f) = Σ_v bv; reason: these are the circulation conditions (nonnegative flow on (v, s), capacities, conservation at s); conservation at every v and saturation of (s, v) hold by construction, and every circulation decomposes into cycles
--   - generalization: strategies satisfying (1), (2) and (3) → only (1) and (3) are assumed; reason: (2) follows from (3), so the source profiles are exactly the instances
--   - encoding: a_e : ℝ≥0 → ℝ≥0 and flows in ℝ≥0 → NNReal; the subtraction fv − Σ f is exact by the first clause; reason: NNReal is ℝ≥0; same instances
--   - generalization: a graph G = (V, E) with a set of directed edges → edges indexed by Fin m with tail and head maps, so parallel edges and self-loops are allowed, and n = 0 or m = 0; reason: the argument is unchanged; on a simple graph the statement is the source's
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, Proposition 5, p. 17 (proof pp. 17–18)

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_cplus

open scoped NNReal

namespace FlowAllocationGames.UnitRanking

/-- **Proposition 5.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, Proposition 5, p. 17:
"For every feasible flow f for a strategy profile a, the corresponding flow for the modified
strategy profile a′ in the extended game G′ can be decomposed and represented as a circulation. The
auxiliary node s has an incoming flow of Σ_{v∈V} bv, and all auxiliary edges (s, v) are
saturated." The construction of `G′` (§3.1, p. 17): an auxiliary node `s`, an edge `(v, s)` of
capacity `∞` and an edge `(s, v)` of capacity `bv` for every `v`; the supply of `v` becomes flow on
`(s, v)`, and the flow not forwarded by `v` goes on `(v, s)`.
Strategies are the paper's general ones (§2.1, pp. 9–10): `a e : ℝ≥0 → ℝ≥0` with the capacity
constraint (1) and the no-fraud constraint (3); `f : E → ℝ≥0` is feasible, (4):
`f e = a e (b_v + Σ_{e'∈E⁻(v)} f e')` with `v` the tail of `e`. Write `out v = Σ_{e∈E⁺(v)} f e`
and `fv = b v + Σ_{e∈E⁻(v)} f e`. The flow on `G′` is `f` on the edges of `G`, `fv − out v` on
`(v, s)` and `b v` on `(s, v)` (so the edges `(s, v)` are saturated). Then:
1. every node forwards at most its total supply, `out v ≤ fv`, so the flow on `(v, s)` is
   nonnegative (and flow is conserved at `v`: `b v + Σ_{E⁻(v)} f = out v + (fv − out v)`);
2. every edge of `G` carries at most its capacity;
3. the incoming flow of `s` is `Σ_v (fv − out v) = Σ_v b v`, which is also the outgoing flow of `s`
   (conservation at `s`).
Together these say that the flow on `G′` is a circulation with saturated edges `(s, v)`.
**Formalization Note.** The real-valued model of §2.1 is taken literally: `ℝ≥0` is the paper's
`ℝ≥0`, and the subtraction `fv − out v` is exact by clause 1. Constraint (2) is not assumed, as it
follows from (3); monotonicity is not assumed (the proof uses only (4) and (3)). "Can be decomposed
and represented as a circulation" is stated as "is a circulation". -/
theorem proposition_5_circulation {n m : ℕ} (Γ : Game n m) (a : Fin m → ℝ≥0 → ℝ≥0)
    (hcap : ∀ e y, a e y ≤ Γ.c e)
    (hnf : ∀ v y, ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v), a e y =
      min (cplus Γ v : ℝ≥0) y)
    (f : Fin m → ℝ≥0)
    (hf : ∀ e, f e = a e ((Γ.b (Γ.tail e) : ℝ≥0) +
      ∑ e' ∈ Finset.univ.filter (fun e' => Γ.head e' = Γ.tail e), f e')) :
    (∀ v, ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v), f e ≤
      (Γ.b v : ℝ≥0) + ∑ e ∈ Finset.univ.filter (fun e => Γ.head e = v), f e) ∧
    (∀ e, f e ≤ Γ.c e) ∧
    ∑ v, ((Γ.b v : ℝ≥0) + ∑ e ∈ Finset.univ.filter (fun e => Γ.head e = v), f e -
      ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v), f e) = ∑ v, (Γ.b v : ℝ≥0) := by sorry

end FlowAllocationGames.UnitRanking
