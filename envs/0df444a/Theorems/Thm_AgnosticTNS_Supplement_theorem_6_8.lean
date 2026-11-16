-- Prove2me | Theorems.Thm_AgnosticTNS_Supplement_theorem_6_8
-- name    : AgnosticTNS.Supplement.theorem_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:47:05.85663+00:00
-- url     : https://prove2.me/theorems/878046c1-3d9d-44f9-bad3-e80bd23931f9
-- title:
--   Theorem 6.8 — entanglement rerouting of a single edge
-- statement:
--   Let $G=([n],E)$ be a graph and $w:E\to\mathbb N$, extended by $w(f)=1$ for pairs $f\notin E$. Let $|\psi\rangle\in S_d(G,w)$, let $e=\{x,y\}\in E$, let $z\in[n]\setminus\{x,y\}$, and set $q:=w(e)$. Define $E':=(E\setminus\{\{x,y\}\})\cup\{\{x,z\},\{y,z\}\}$, $G'=([n],E')$, and
--   $$
--   w'(f)=\begin{cases} q\,w(\{x,z\}), & f=\{x,z\},\\ q\,w(\{y,z\}), & f=\{y,z\},\\ w(f), & \text{otherwise.}\end{cases}
--   $$
--   Then $|\psi\rangle\in S_d(G',w')$ (6.9), and the new representation has maximum bond dimension $\chi':=\max(\{1\}\cup\{w'(f):f\in E'\})$, i.e. $|\psi\rangle\in S_d(G',\chi')$ (6.10).
--
--   The move changes the graph of a tensor network representation without changing the state, at the cost of multiplying two bond dimensions by $q$; iterated, it converts general tensor networks into MPS and TTN representations.
--
--   **Formalization Note** Whether $\{x,z\}$ or $\{y,z\}$ already belong to $E$ is not assumed either way.
--
--   Differences from the source:
--   - reading: (6.10) the maximum bond dimension of the new representation is χ′ → ψ ∈ S_d(G′, χ′) with χ′ = max 1 (sup of w′ over E′); reason: the mathematical content of the sentence: the representation on (G′, w′) has all bonds ≤ χ′
--   - encoding: w extended by 1 off E; G′ = ([n], E′) → extW; SimpleGraph.fromEdgeSet; reason: fromEdgeSet discards only diagonal pairs, none of which occur since x ≠ y and z ∉ {x, y}
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.8, Eqs. (6.6)–(6.10), p.49

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_rerouteWeight
import Definitions.Def_AgnosticTNS_TNSchi

namespace AgnosticTNS.Supplement

/-- **Theorem 6.8 (Entanglement rerouting)**, p.49 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
Let `G = ([n], E)`, `w : E → ℕ`, extended to all pairs of distinct vertices by `w(f) = 1` for `f ∉ E`.
Let `|ψ⟩ ∈ S_d(G, w)`, `e = {x, y} ∈ E`, `z ∈ [n] ∖ {x, y}`, `q := w(e)` (6.6). With
`E′ := (E ∖ {{x, y}}) ∪ {{x, z}, {y, z}}` (6.7), `w′({x, z}) = q w({x, z})`, `w′({y, z}) = q w({y, z})`,
`w′(f) = w(f)` otherwise (6.8), and `G′ = ([n], E′)`: `|ψ⟩ ∈ S_d(G′, w′)` (6.9). Moreover, the maximum bond
dimension of the new representation is `χ′ := max({1} ∪ {w′(f) : f ∈ E′})` (6.10).

**Formalization Note** (6.10) is stated as `|ψ⟩ ∈ S_d(G′, χ′)` with `χ′ = max 1 (sup_{f ∈ E′} w′(f))`
(`sSup` of the finite range; `0` when `E′` is empty). Neither `{x, z}` nor `{y, z}` is assumed absent or
present in `E`. -/
theorem theorem_6_8 (n d : ℕ) (G : SimpleGraph (Fin n)) (w : G.edgeSet → ℕ)
    (ψ : (Fin n → Fin d) → ℂ) (hψ : ψ ∈ TNS d G w) (x y z : Fin n) (hxy : G.Adj x y)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    ψ ∈ TNS d (rerouteGraph G x y z) (rerouteWeight G w x y z) ∧
      ψ ∈ TNSchi d (rerouteGraph G x y z) (max 1 (sSup (Set.range (rerouteWeight G w x y z)))) := by sorry

end AgnosticTNS.Supplement
