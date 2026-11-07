-- Prove2me | Theorems.Thm_DoublingMST_lemma_3_3
-- name    : DoublingMST.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:26.825466+00:00
-- url     : https://prove2.me/theorems/fdb3144c-35b9-4616-81d8-a96b40a5405f
-- title:
--   Lemma 3.3 (1)–(5) and the t-WSPC clause — properties of Algorithm 1's output (time clauses: lemma_3_3_time)
-- statement:
--   There is an absolute constant $C>0$ with the following property. Assume $|X|\ge2$ and minimum interpoint distance $>1$, let $N$ be a net hierarchy (§2.1), let $t\ge32$, and let $\Psi$ be **any** output of Algorithm 1 on $N$ with parameter $t$. Then:
--
--   1. (bounded level difference) every $(u,v)\in\Psi$ has $|\operatorname{lev}(u)-\operatorname{lev}(v)|\le1$;
--   2. (separation) every $(u,v)\in\Psi$ has $d(u,v)>(2t+2)\max\{2^{\operatorname{lev}(u)},2^{\operatorname{lev}(v)}\}$, or $\operatorname{lev}(u)=\operatorname{lev}(v)=0$;
--   3. (covering) for any two distinct points $x,y$ some $(u,v)\in\Psi$ has one of them in $B(u,2^{\operatorname{lev}(u)})$ and the other in $B(v,2^{\operatorname{lev}(v)})$;
--   4. (bounded degree) every net point appears in at most $t^{C\operatorname{ddim}(X)}$ pairs of $\Psi$;
--   5. (few near neighbours) for every $T\subseteq X$, at most $t^{C\operatorname{ddim}(X)}|T|$ pairs $(u,v)\in\Psi$ satisfy $d(u,T)\le2^{\operatorname{lev}(u)+2}$ and $d(v,T)\le2^{\operatorname{lev}(v)+2}$; and $|\Psi|\le t^{C\operatorname{ddim}(X)}n$;
--   6. $\Phi=\{(B(u,2^{\operatorname{lev}(u)}),B(v,2^{\operatorname{lev}(v)})):(u,v)\in\Psi\}$ is a $t$-WSPC of $X$.
--
--   Property (5) is the new ingredient of the paper's running-time analysis.
--
--   **Formalization Note** This item contains the structural clauses of Lemma 3.3 only; its two running-time clauses are not part of it (see below).
--
--   Differences from the source:
--
--   - encoding: an n-point metric space (X, d) → points Fin n with d : Fin n → Fin n → ℝ satisfying IsMetric; reason: finite metric spaces up to relabelling; same instances
--   - encoding: the standing assumption |X| ≥ 2 of §2 (p.11) → hypothesis 2 ≤ n on the number of points; reason: the source assumes it throughout; it excludes only the one-point space
--   - encoding: the §2.1 standing assumption that the minimum interpoint distance of X is greater than 1 (p.12) → hypothesis MinDistGtOne d; reason: the source assumes it throughout §§2.1–4 (it is what makes level-0 balls singletons)
--   - reading: Lemma 3.3: there is an algorithm that computes, in t^{O(ddim)}n log ∆ time, a collection Ψ with (1)–(5), and Φ is a t-WSPC constructible in t^{O(ddim)}n log ∆ time → for every output Ψ of Algorithm 1 on the hierarchy: (1)–(5) and "Φ is a t-WSPC"; the two running-time clauses are the companion item DoublingMST.lemma_3_3_time, stated for the same outputs Ψ; reason: the paper proves and cites the clauses (1)–(5) separately ("Proof of Lemma 3.3 (5)", "(4) of Lemma 3.3"); the time clauses need a machine and a memory layout, the clauses (1)–(5) neither; the title names the companion
--   - reading: the collection Ψ computed by the algorithm → every output of every run of Algorithm 1 (any order of the recursive calls); reason: the marks make the output order-dependent; the properties hold for every run
--   - encoding: ddim(X) ≤ ddim → ddim(X) itself; reason: t^{C·D} is monotone in D, so the two are equivalent
--   - reading: t^{O(ddim)} → ∃ C > 0, chosen before the space and before t, with bound t^{C · ddim(X)}; reason: the standard meaning of the O; one absolute constant for every t ≥ 32
--   - encoding: d(u, T) ≤ r → u ∈ B(T, r); reason: the same condition for nonempty T; for T = ∅ both are false (min ∅ = +∞)
--   - encoding: each net point u appears in at most … pairs → for every w : Fin n × ℕ, the number of pairs with first or second entry w; reason: elements are pairs (point, level); a non-element appears in no pair
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 3.3 (1)–(5) and the "In particular" clause, pp.14–15 (PDF pp.16–17); proofs of (5) pp.15–16 and of (1)–(4) in Appendix C

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_MinDistGtOne
import Definitions.Def_DoublingMST_ddim
import Definitions.Def_DoublingMST_ball
import Definitions.Def_DoublingMST_nbhd
import Definitions.Def_DoublingMST_IsWSPC
import Definitions.Def_DoublingMST_IsAlg1Output
open scoped Classical

namespace DoublingMST

/-- **Lemma 3.3 (1)–(5) and the t-WSPC clause (properties of Algorithm 1's output).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 3.3, pp.14–15 (PDF pp.16–17): "There is an algorithm that, given as input a metric
space (X, d) with ddim(X) ≤ ddim and minimum interpoint distance greater than 1 and diameter ∆, a
net hierarchy N over X as in Section 2.1, and a parameter t ≥ 32, computes in t^{O(ddim)} n log ∆
time a collection Ψ of pairs of net points, such that each pair (u, v) ∈ Ψ satisfies the following:
(1) Bounded level difference: |lev(u) − lev(v)| ≤ 1. (2) Separation: Either
d(u, v) > (2t + 2) · max{2^{lev(u)}, 2^{lev(v)}} or lev(u) = lev(v) = 0. (3) Covering: For any two
distinct points x, y ∈ X, there exists at least one pair (u, v) ∈ Ψ such that x is in either
B(u, 2^{lev(u)}) or B(v, 2^{lev(v)}) and y in the other set. (4) Bounded degree: Each net point u
appears in at most t^{O(ddim)} pairs in Ψ. (5) Few near neighbors: For each subset T of X, there are
at most t^{O(ddim)}|T| pairs (u, v) ∈ Ψ such that d(u, T) ≤ 2^{lev(u)+2} and d(v, T) ≤ 2^{lev(v)+2}
hold simultaneously. Consequently, |Ψ| ≤ t^{O(ddim)}n. In particular, Φ = {(B(u, 2^{lev(u)}),
B(v, 2^{lev(v)})) : (u, v) ∈ Ψ} is a t-WSPC of X, and it can be constructed in time
t^{O(ddim)}n log ∆."

There is an absolute `C > 0` such that, under the standing assumptions of §2.1, for every net
hierarchy `H`, every `t ≥ 32` and **every** output `Ψ` of Algorithm 1 on `H` with parameter `t`:
1. every `(u, v) ∈ Ψ` has `|lev u − lev v| ≤ 1`;
2. every `(u, v) ∈ Ψ` has `d(u, v) > (2t + 2) max{2^{lev u}, 2^{lev v}}`, or `lev u = lev v = 0`;
3. any two distinct points `x, y` are split by some `(u, v) ∈ Ψ`: one lies in `B(u, 2^{lev u})`
   and the other in `B(v, 2^{lev v})`;
4. every element `w` lies in at most `t^{C·ddim(X)}` pairs of `Ψ`;
5. for every `T ⊆ X`, at most `t^{C·ddim(X)}|T|` pairs `(u, v) ∈ Ψ` have `d(u, T) ≤ 2^{lev u + 2}` and
   `d(v, T) ≤ 2^{lev v + 2}`; and `|Ψ| ≤ t^{C·ddim(X)} n`;
6. `Φ = {(B(u, 2^{lev u}), B(v, 2^{lev v})) : (u, v) ∈ Ψ}` is a t-WSPC of `X`.

**Formalization Note.** The running-time clauses are the companion item
`DoublingMST.lemma_3_3_time`. `d(u, T) ≤ r` is `u ∈ nbhd d T r` (false for `T = ∅`, so
clause 5 then counts no pair). A "net point u" of (4) is an element `(point, level)`; (4) is stated
for every `w : Fin n × ℕ` (non-elements appear in no pair). One `C` serves every `t ≥ 32`. -/
theorem lemma_3_3 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ d : Fin n → Fin n → ℝ, IsMetric d →
    MinDistGtOne d → ∀ (H : NetHierarchy d) (t : ℝ), 32 ≤ t →
    ∀ Ψ : Finset ((Fin n × ℕ) × (Fin n × ℕ)), IsAlg1Output H t Ψ →
      (∀ uv ∈ Ψ, |(uv.1.2 : ℤ) - (uv.2.2 : ℤ)| ≤ 1) ∧
      (∀ uv ∈ Ψ, (2 * t + 2) * max ((2 : ℝ) ^ uv.1.2) ((2 : ℝ) ^ uv.2.2) < d uv.1.1 uv.2.1 ∨
        (uv.1.2 = 0 ∧ uv.2.2 = 0)) ∧
      (∀ x y : Fin n, x ≠ y → ∃ uv ∈ Ψ,
        (x ∈ ball d uv.1.1 ((2 : ℝ) ^ uv.1.2) ∧ y ∈ ball d uv.2.1 ((2 : ℝ) ^ uv.2.2)) ∨
        (y ∈ ball d uv.1.1 ((2 : ℝ) ^ uv.1.2) ∧ x ∈ ball d uv.2.1 ((2 : ℝ) ^ uv.2.2))) ∧
      (∀ w : Fin n × ℕ, ((Ψ.filter fun uv => uv.1 = w ∨ uv.2 = w).card : ℝ) ≤
        t ^ (C * ddim d)) ∧
      (∀ T : Finset (Fin n), ((Ψ.filter fun uv =>
          uv.1.1 ∈ nbhd d T ((2 : ℝ) ^ (uv.1.2 + 2)) ∧
          uv.2.1 ∈ nbhd d T ((2 : ℝ) ^ (uv.2.2 + 2))).card : ℝ) ≤ t ^ (C * ddim d) * T.card) ∧
      ((Ψ.card : ℝ) ≤ t ^ (C * ddim d) * n) ∧
      IsWSPC d (Ψ.image fun uv => (ball d uv.1.1 ((2 : ℝ) ^ uv.1.2),
        ball d uv.2.1 ((2 : ℝ) ^ uv.2.2))) t := by sorry

end DoublingMST
