-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_lemma_14
-- name    : FacilityIncompatibilities.UniformMatroid.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:34.816817+00:00
-- url     : https://prove2.me/theorems/c4162073-fa31-4703-8800-05f52f1fe137
-- title:
--   Lemma 14 — if |O| < |S| then P ⊆ μ(O) (= Theorem 11)
-- statement:
--   Let $(V_C,V_F,d,f,\mathcal M)$ be an FL-MI instance, $S,O\subseteq V_F$ with $|O|<|S|$, $\sigma_O$ a minimum-cost feasible assignment to $O$, and $\mu:O\to S$ a minimum-cost injection with $\mu(i)=i$ for every $i\in O\cap S$. Let $\pi$ be a feasible assignment to $S$ minimizing $W(\pi)=\sum_j d(\sigma_O(j),\pi(j))$ and, among those, minimizing $q(\pi)=|\{j:\pi(j)\notin\mu(O)\}|$. Then the image $P=\pi(V_C)$ satisfies
--
--   $$P\subseteq\mu(O).$$
--
--   In particular $|P|\le|O|$, which is the key to bounding the opening cost of $P$ (Lemma 15). Theorem 11 (printed p.10) announces the same statement.
--
--   Differences from the source:
--   - generalization: metric distances d on V_C ∪ V_F (Definition 1) → a pseudometric: d(x,x)=0, symmetry and the triangle inequality, distinct points may be at distance 0; reason: every metric satisfies these axioms, so every instance of the source is covered
--   - generalization: O a fixed globally optimal solution with optimal assignment σ_O (§2.1, printed p.5) → O any facility set with a minimum-cost feasible assignment σ_O (any feasible O); reason: §3 (printed p.13) states the analysis does not require optimality of O and uses it for a non-optimal O after rescaling; an optimum is a special case
--   - generalization: S the fixed locally optimal solution of §2.1 → any facility set S admitting the feasible assignment π; reason: the proof uses no local optimality of S; the §2.1 S is a special case
--   - encoding: an injection μ : O → S → a function μ : F → F with μ(O) ⊆ S and injective on O; values off O are irrelevant; reason: Lean convention; the same injections
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Lemma 14, printed p.11 / PDF p.12 (= Theorem 11, printed p.10 / PDF p.11); proof printed pp.11–13 / PDF pp.12–14

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Compression

namespace FacilityIncompatibilities.UniformMatroid

/-- **Lemma 14** (printed p.11 / PDF p.12; announced as Theorem 11, printed p.10): with `σ_O`,
the injection `μ` and the tie-broken `W`-minimizer `π` of §2.1, if `|O| < |S|` then
`P = π(V_C) ⊆ μ(O)`. -/
theorem lemma_14 {C F : Type*} [Fintype C] [Fintype F] [DecidableEq F] (I : Instance C F)
    (hI : I.Valid) (S O : Finset F) (σO : C → F) (μ : F → F) (π : C → F)
    (hσO : I.IsOptAssignment O σO) (hlt : O.card < S.card)
    (hμ : I.IsSection21Injection O S μ) (hπ : I.IsTieBrokenWMin S O σO μ π) :
    assignImage π ⊆ O.image μ := by sorry

end FacilityIncompatibilities.UniformMatroid
