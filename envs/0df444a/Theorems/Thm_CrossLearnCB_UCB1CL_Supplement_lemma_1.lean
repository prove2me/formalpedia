-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_Supplement_lemma_1
-- name    : CrossLearnCB.UCB1CL.Supplement.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:51:24.87062+00:00
-- url     : https://prove2.me/theorems/30f81ea1-b749-461a-b12e-471adf596b76
-- title:
--   Lemma 1, p. 13 — λ(G) is the supremum of Σ_v f(v)/Σ_{w∈I(v)} f(w) over nonnegative weights f
-- statement:
--   Let $G$ be a directed graph on a finite vertex set $V$ that contains every self-loop $v \to v$, and let $I(v) = \{w \in V : w \to v\}$ be the in-neighbourhood of $v$ (so $v \in I(v)$). Let $\lambda(G)$ be the maximum acyclic subgraph number (Definition 3). Then
--
--   $$\lambda(G) = \sup_{f : V \to \mathbb R_+} \ \sum_{v \in V} \frac{f(v)}{\sum_{w \in I(v)} f(w)} .$$
--
--   That is, $\lambda(G)$ is an upper bound of these sums for every nonnegative weight function $f$, and no smaller number is.
--
--   This identity turns the variance terms in the analyses of EXP3.CL and EXP3.CL-U, which are sums of this form with $f(c) = \Pr[c]\,p_{i,t}(c)$ or $f = D$, into the graph quantity $\lambda$.
--
--   **Formalization Note** The supremum is stated as `IsLUB` of the set of values, so no boundedness is presupposed. A term with $f(v) = 0$ is $0$ (Lean's $x/0 = 0$); a term with $f(v) > 0$ has denominator at least $f(v)$ because of the self-loop.
--
--   Differences from the source:
--   - encoding: directed graphs with self-loops on a vertex set V (all graphs of the paper are finite) → a relation on a finite type V with H v v for every v; reason: same instances
--   - encoding: λ(G) = sup → IsLUB of the set of values at λ(G); reason: the supremum of a set of reals is its least upper bound, stated without presupposing boundedness
--   - reading: f : V → R₊ with 0/0 terms undefined → f ≥ 0 on all of V, and a term with f(v) = 0 counts as 0; reason: Self-loops make every positive-weight denominator positive. Zero weights may be deleted, giving the same expression on the induced positive support; its maximum acyclic number is at most that of G. The strictly positive weights in Appendix C.3 already approach λ(G). Thus adjoining zero weights with zero summands leaves the supremum unchanged; this is not a claim of continuity at 0/0.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 13, Lemma 1; proof p. 49, App. C.3

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_AcyclicNumber

namespace CrossLearnCB.UCB1CL.Supplement

open Classical in
/-- Lemma 1, p. 13: for a finite directed graph `H` with all self-loops, `λ(H)` is the least
upper bound of `Σ_v f(v) / Σ_{w ∈ I(v)} f(w)` over all nonnegative weights `f`, where
`I(v) = {w | w → v}`. -/
theorem lemma_1 {V : Type*} [Fintype V] (H : V → V → Prop) (hH : ∀ v, H v v) :
    IsLUB {x : ℝ | ∃ f : V → ℝ, (∀ v, 0 ≤ f v) ∧
        x = ∑ v, f v / ∑ w ∈ Finset.univ.filter (fun w => H w v), f w}
      (maxAcyclicNumber H : ℝ) := by sorry

end CrossLearnCB.UCB1CL.Supplement
