-- Prove2me | Theorems.Thm_CountingLLL_DetCount_theorem_2_2
-- name    : CountingLLL.DetCount.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:21.00006+00:00
-- url     : https://prove2.me/theorems/a7614b8d-968e-40a7-b913-2f22afd3d2ea
-- title:
--   Theorem 2.2 — conditional LLL bound [HSS11]
-- statement:
--   Let $\Phi$ be a CSP formula and $\mathcal E$ a family of its constraints. Suppose $x\in(0,1)^{\mathcal E}$ satisfies the LLL condition (6) for $\mathcal E$:
--   $$\mathbb P[\neg c]\le x(c)\prod_{c'\in\mathcal E\setminus\{c\},\ \mathrm{vbl}(c)\cap\mathrm{vbl}(c')\ne\emptyset}(1-x(c'))\qquad(c\in\mathcal E).$$
--   Let $A$ be an event determined by the assignment on a set of variables $W=\mathrm{vbl}(A)\subseteq V$, that is, $A(\sigma)=A(\sigma')$ whenever $\sigma$ and $\sigma'$ agree on $W$. Then
--   $$\mathbb P[A\mid\mathcal E]\le\mathbb P[A]\prod_{c\in\mathcal E,\ \mathrm{vbl}(c)\cap W\ne\emptyset}(1-x(c))^{-1}.$$
--
--   This controls local events under the uniform distribution on solutions; it gives Lemma 3.1 and the bound (15) inside Lemma 3.6.
--
--   Differences from the source:
--   - generalization: the whole constraint set C of the formula → any constraint family E of the formula, with (6) and the product taken inside E; reason: E = all constraints is the source statement; a family E is the constraint set of the subformula (V, Q, E), to which the paper applies the theorem
--   - encoding: x ∈ (0,1)^C → x : Fin m → ℝ with 0 < x c < 1 for c ∈ E; reason: values outside E are never used
--   - encoding: an event A determined by vbl(A) ⊆ V → a predicate A on configurations and a variable set W such that A agrees on configurations that agree on W; reason: same notion; W is any such set, not necessarily the minimal one
--   - encoding: uniform product measure P on Q and P[A | B] → counting ratio |{σ : A σ}| / |Q| and P[A ∧ B] / P[B]; reason: the same measure on a finite product; every conditioning event in the statement has positive probability under its hypotheses
--   - generalization: standing assumption q ≥ 2, k ≥ 2, D ≥ 1 (PDF 3) → not assumed; reason: the identity or conditional LLL bound uses only the stated hypotheses, which guarantee positive conditioning probabilities; every source instance is covered
--   - encoding: finite variables V and finite domains Q_v → V = Fin n and Q_v = Fin (q v), with q v ≥ 2; reason: every finite source variable space is relabelled bijectively; no constraint function or scope is restricted
--   - generalization: a finite set of constraints C → constraints indexed by Fin m, permitting equal scopes and predicates at different indices; reason: enumerating a source constraint set gives an instance with distinct indices; allowing repetitions preserves that full source case
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Theorem 2.2 ([HSS11, Theorem 2.1]), PDF p. 7 (printed p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_CSP

set_option autoImplicit false

namespace CountingLLL.DetCount

open CSP

/-- Theorem 2.2 ([HSS11, Theorem 2.1]), for the constraint family `E` of the formula `Φ`
(`E = univ` is the paper's statement). If `x ∈ (0,1)^E` satisfies the LLL condition (6),
`P[¬c] ≤ x(c) ∏_{c' ∈ E∖{c}, vbl(c)∩vbl(c')≠∅} (1 − x(c'))` for all `c ∈ E`, and the event `A`
is determined by the assignment on the variable set `W`, then
`P[A | E] ≤ P[A] ∏_{c ∈ E, vbl(c) ∩ W ≠ ∅} (1 − x(c))⁻¹`. -/
theorem theorem_2_2 (Φ : CSP) (E : Finset (Fin Φ.m)) (x : Fin Φ.m → ℝ)
    (hx : ∀ c ∈ E, 0 < x c ∧ x c < 1)
    (h6 : ∀ c ∈ E, Φ.prob (fun σ => ¬ Φ.Sat c σ) ≤ x c * ∏ c' ∈ Φ.nbr E c, (1 - x c'))
    (A : Φ.Config → Prop) (W : Finset (Fin Φ.n))
    (hA : ∀ σ σ' : Φ.Config, (∀ v ∈ W, σ v = σ' v) → (A σ ↔ A σ')) :
    Φ.condProb A (Φ.SatAll E) ≤
      Φ.prob A * ∏ c ∈ E.filter (fun c => ¬ Disjoint (Φ.scope c) W), (1 - x c)⁻¹ := by sorry

end CountingLLL.DetCount
